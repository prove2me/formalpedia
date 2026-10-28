-- Prove2me | solution 1 for SensitivityRowCounting.shared_labeling_12607
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:45:18.586462+00:00
-- url     : https://prove2.me/submissions/89c50a56-8f75-410f-8331-f8b7df104c23

import Mathlib
open scoped Classical BigOperators
namespace SLSol

def G : ℕ → ℕ → ℕ
  | 0, _ => 1
  | q+1, d => G q d + d.descFactorial (q+1) / (q+1).factorial

theorem G_eq (q d : ℕ) : G q d = ∑ a ∈ Finset.range (q+1), d.choose a := by
  induction q with
  | zero => simp [G]
  | succ q ih => rw [Finset.sum_range_succ, ← ih, G, Nat.choose_eq_descFactorial_div_factorial]

theorem card_P {α : Type*} (S : Finset α) (q : ℕ) :
    (S.powerset.filter (fun s => s.card ≤ q)).card = G q S.card := by
  rw [G_eq, Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range (q+1))]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.card_powersetCard]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    simp only [Finset.mem_range] at ha
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  · intro s hs
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs
    simp only [Finset.coe_range, Set.mem_Iio]
    omega

noncomputable section

def other (c : Fin 2) : Fin 2 := if c = 0 then 1 else 0

theorem eq_other_of_ne (c d : Fin 2) (h : d ≠ c) : d = other c := by
  fin_cases c <;> fin_cases d <;> simp [other] at *

variable {k : ℕ}

def internalEdges (A : Fin k → Fin k → Prop) (I : Finset (Fin k)) : Finset (Fin k × Fin k) :=
  (I ×ˢ I).filter fun p => A p.1 p.2

theorem card_internalEdges (A : Fin k → Fin k → Prop) (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i)) (I : Finset (Fin k)) :
    (internalEdges A I).card = I.card.choose 2 := by
  have ne_of_adj : ∀ {i j}, A i j → i ≠ j := by
    rintro i j h rfl; exact hloop i h
  let U := internalEdges A I
  let V := (I ×ˢ I).filter fun p => A p.2 p.1
  have hd : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h1 := (Finset.mem_filter.mp hp).2
    exact (hcomp (ne_of_adj h1)).mp h1 (Finset.mem_filter.mp hq).2
  have hu : U.disjUnion V hd = I.offDiag := by
    ext ⟨i,j⟩
    simp only [Finset.mem_disjUnion, U, V, internalEdges, Finset.mem_filter,
      Finset.mem_product, Finset.mem_offDiag]
    constructor
    · rintro (⟨⟨hi,hj⟩,h⟩ | ⟨⟨hi,hj⟩,h⟩)
      · exact ⟨hi,hj,ne_of_adj h⟩
      · exact ⟨hi,hj,(ne_of_adj h).symm⟩
    · rintro ⟨hi,hj,hne⟩
      by_cases hh : A j i
      · exact Or.inr ⟨⟨hi,hj⟩,hh⟩
      · exact Or.inl ⟨⟨hi,hj⟩,(hcomp hne).mpr hh⟩
  have hs : U.card = V.card := Finset.card_equiv (Equiv.prodComm (Fin k) (Fin k)) (by
    intro p
    simp only [U,V,internalEdges,Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
    tauto)
  have hc := congrArg Finset.card hu
  rw [Finset.card_disjUnion, ← hs, Finset.offDiag_card] at hc
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  change U.card = _
  omega

theorem sum_out (A : Fin k → Fin k → Prop) (I : Finset (Fin k)) :
    ∑ i ∈ I, (I.filter fun j => A i j).card = (internalEdges A I).card := by
  rw [internalEdges, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_filter]

def good (A : Fin k → Fin k → Prop) (I : Finset (Fin k)) (m : Fin k → Fin 2)
    (e : Fin k → Finset (Fin k)) : Finset (Fin k → Fin k → Fin 2) :=
  Finset.univ.filter fun a => ∀ p ∈ internalEdges A I,
    a p.1 p.2 = if p.2 ∈ e p.1 then other (m p.2) else m p.2

theorem good_card_le (A : Fin k → Fin k → Prop) (I : Finset (Fin k)) (m : Fin k → Fin 2)
    (e : Fin k → Finset (Fin k)) :
    (good A I m e).card ≤ 2 ^ (k*k - (internalEdges A I).card) := by
  let S := internalEdges A I
  let f : (Fin k → Fin k → Fin 2) → ((Sᶜ : Finset _) → Fin 2) :=
    fun a p => a p.1.1 p.1.2
  have hinj : Set.InjOn f (good A I m e) := by
    intro a ha b hb hab
    simp only [good, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    funext i j
    by_cases hpair : (i,j) ∈ S
    · rw [ha _ hpair, hb _ hpair]
    · exact congrFun hab ⟨(i,j), Finset.mem_compl.2 hpair⟩
  calc
    (good A I m e).card ≤ (Finset.univ : Finset ((Sᶜ : Finset _) → Fin 2)).card :=
      Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
    _ = 2 ^ (k*k - (internalEdges A I).card) := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Finset.card_compl,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

def Mset (I : Finset (Fin k)) : Finset (Fin k → Fin 2) :=
  Fintype.piFinset fun j => if j ∈ I then Finset.univ else {0}

def Pset (A : Fin k → Fin k → Prop) (I : Finset (Fin k)) (q : ℕ) (i : Fin k) :
    Finset (Finset (Fin k)) :=
  (I.filter fun j => A i j).powerset.filter fun s => s.card ≤ q

def Eset (A : Fin k → Fin k → Prop) (I : Finset (Fin k)) (q : ℕ) :
    Finset (Fin k → Finset (Fin k)) :=
  Fintype.piFinset fun i => if i ∈ I then Pset A I q i else {∅}

theorem card_Mset (I : Finset (Fin k)) : (Mset I).card = 2 ^ I.card := by
  rw [Mset, Fintype.card_piFinset]
  have : ∀ j, (if j ∈ I then (Finset.univ : Finset (Fin 2)) else {0}).card
      = if j ∈ I then 2 else 1 := by
    intro j; split_ifs <;> simp
  simp only [this]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem card_Eset (A : Fin k → Fin k → Prop) (I : Finset (Fin k)) (q : ℕ) :
    (Eset A I q).card = ∏ i ∈ I, G q (I.filter fun j => A i j).card := by
  rw [Eset, Fintype.card_piFinset]
  have : ∀ i, (if i ∈ I then Pset A I q i else {∅}).card
      = if i ∈ I then G q (I.filter fun j => A i j).card else 1 := by
    intro i; split_ifs
    · rw [Pset, card_P]
    · simp
  simp only [this]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

def BadSet (A : Fin k → Fin k → Prop) (q t : ℕ) : Finset (Fin k → Fin k → Fin 2) :=
  (Finset.powersetCard t Finset.univ).biUnion fun J =>
    (Mset J).biUnion fun m => (Eset A J q).biUnion fun e => good A J m e

theorem mem_BadSet (A : Fin k → Fin k → Prop) (a : Fin k → Fin k → Fin 2) (q t : ℕ)
    (I : Finset (Fin k)) (colors : Fin k → Fin 2)
    (h : ∀ i ∈ I, (I.filter (fun j => A i j ∧ a i j ≠ colors j)).card ≤ q)
    (ht : t ≤ I.card) : a ∈ BadSet A q t := by
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq ht
  simp only [BadSet, Finset.mem_biUnion]
  refine ⟨J, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hJ⟩,
    fun j => if j ∈ J then colors j else 0, ?_,
    fun i => if i ∈ J then J.filter (fun j => A i j ∧ a i j ≠ colors j) else ∅, ?_, ?_⟩
  · rw [Mset, Fintype.mem_piFinset]
    intro j; split_ifs <;> simp
  · rw [Eset, Fintype.mem_piFinset]
    intro i
    split_ifs with hi
    · rw [Pset, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · intro j hj
        simp only [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, hj.2.1⟩
      · refine le_trans (Finset.card_le_card ?_) (h i (hJI hi))
        intro j hj
        simp only [Finset.mem_filter] at hj ⊢
        exact ⟨hJI hj.1, hj.2⟩
    · simp
  · simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨i, j⟩ hp
    simp only [internalEdges, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hi, hj⟩, hij⟩ := hp
    simp only [hi, hj, if_true, Finset.mem_filter, true_and]
    by_cases hn : a i j = colors j
    · simp [hn]
    · rw [if_pos ⟨hij, hn⟩]
      exact eq_other_of_ne _ _ hn

theorem prod_bound {ι : Type*} (J : Finset ι) (d : ι → ℕ) (F : ℕ → ℕ) (a b M t ds : ℕ)
    (hJ : J.card = t) (hd : ∀ i ∈ J, d i ≤ t)
    (htan : ∀ x, x < t + 1 → F x * b ^ x * a ^ ds ≤ M * a ^ x * b ^ ds) :
    (∏ i ∈ J, F (d i)) * (b ^ (∑ i ∈ J, d i) * a ^ (t * ds))
      ≤ M ^ t * a ^ (∑ i ∈ J, d i) * b ^ (t * ds) := by
  have h1 : (∏ i ∈ J, F (d i)) * (b ^ (∑ i ∈ J, d i) * a ^ (t * ds))
      = ∏ i ∈ J, (F (d i) * b ^ (d i) * a ^ ds) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.prod_const, hJ, ← pow_mul, mul_comm ds t, mul_assoc]
  have h2 : M ^ t * a ^ (∑ i ∈ J, d i) * b ^ (t * ds)
      = ∏ i ∈ J, (M * a ^ (d i) * b ^ ds) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.prod_const, Finset.prod_const, hJ, ← pow_mul, mul_comm ds t]
  rw [h1, h2]
  exact Finset.prod_le_prod' fun i hi => htan _ (Nat.lt_succ_of_le (hd i hi))

theorem card_BadSet (A : Fin k → Fin k → Prop) (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i)) (q t a b ds : ℕ) (ha : 0 < a) (hb : 0 < b)
    (htan : ∀ x, x < t + 1 → G q x * b ^ x * a ^ ds ≤ b * a ^ x * b ^ ds) :
    (BadSet A q t).card ≤ k.choose t * 2 ^ t *
      ((b ^ t * a ^ (t.choose 2) * b ^ (t * ds)) / (b ^ (t.choose 2) * a ^ (t * ds)))
      * 2 ^ (k * k - t.choose 2) := by
  set Y := (b ^ t * a ^ (t.choose 2) * b ^ (t * ds)) / (b ^ (t.choose 2) * a ^ (t * ds))
  unfold BadSet
  refine le_trans Finset.card_biUnion_le ?_
  have hJ : ∀ J ∈ Finset.powersetCard t (Finset.univ : Finset (Fin k)),
      ((Mset J).biUnion fun m => (Eset A J q).biUnion fun e => good A J m e).card
        ≤ 2 ^ t * Y * 2 ^ (k * k - t.choose 2) := by
    intro J hJ
    rw [Finset.mem_powersetCard] at hJ
    have hE : (Eset A J q).card ≤ Y := by
      rw [card_Eset]
      apply (Nat.le_div_iff_mul_le (by positivity)).2
      have hs := sum_out A J
      rw [card_internalEdges A hloop hcomp, hJ.2] at hs
      have := prod_bound J (fun i => (J.filter fun j => A i j).card) (G q) a b b t ds hJ.2
        (fun i _ => hJ.2 ▸ Finset.card_filter_le _ _) htan
      rw [hs] at this
      exact this
    calc _ ≤ ∑ m ∈ Mset J, ((Eset A J q).biUnion fun e => good A J m e).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ m ∈ Mset J, ∑ e ∈ Eset A J q, (good A J m e).card :=
          Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le
      _ ≤ ∑ m ∈ Mset J, ∑ e ∈ Eset A J q, 2 ^ (k * k - t.choose 2) := by
          apply Finset.sum_le_sum; intro m _; apply Finset.sum_le_sum; intro e _
          have := good_card_le A J m e
          rwa [card_internalEdges A hloop hcomp, hJ.2] at this
      _ = 2 ^ t * (Eset A J q).card * 2 ^ (k * k - t.choose 2) := by
          rw [Finset.sum_const, Finset.sum_const, card_Mset, hJ.2, smul_eq_mul, smul_eq_mul,
            mul_assoc]
      _ ≤ 2 ^ t * Y * 2 ^ (k * k - t.choose 2) := by gcongr
  calc _ ≤ ∑ J ∈ Finset.powersetCard t (Finset.univ : Finset (Fin k)),
        2 ^ t * Y * 2 ^ (k * k - t.choose 2) := Finset.sum_le_sum hJ
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
      ring

end

def T : Fin 5 → ℕ := ![24,31,38,44,50]
def ds (q : Fin 5) : ℕ := (T q - 1) / 2
def ta (q : Fin 5) : ℕ := G q.val (ds q + 1)
def tb (q : Fin 5) : ℕ := G q.val (ds q)
def CC (q : Fin 5) : ℕ := (T q).descFactorial 2 / 2
def Y (q : Fin 5) : ℕ :=
  (tb q ^ T q * ta q ^ CC q * tb q ^ (T q * ds q)) / (tb q ^ CC q * ta q ^ (T q * ds q))
def Bn (k : ℕ) (q : Fin 5) : ℕ := k.descFactorial (T q) / (T q).factorial

theorem tangent : ∀ q : Fin 5, ∀ x, x < T q + 1 →
    G q.val x * tb q ^ x * ta q ^ ds q ≤ tb q * ta q ^ x * tb q ^ ds q := by
  decide +kernel

theorem budget : ∑ q : Fin 5, Bn 12607 q * 2 ^ T q * Y q * 2 ^ (1225 - CC q) < 2 ^ 1225 := by
  decide +kernel

theorem CC_eq (q : Fin 5) : (T q).choose 2 = CC q := by
  rw [CC, Nat.choose_eq_descFactorial_div_factorial]; rfl

theorem CC_le (q : Fin 5) : CC q ≤ 1225 := by
  revert q; decide +kernel

theorem pos_ab (q : Fin 5) : 0 < ta q ∧ 0 < tb q := by
  revert q; decide +kernel

theorem bad_card {k : ℕ} (hk : 1225 ≤ k * k) (A : Fin k → Fin k → Prop) (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i)) (q : Fin 5) :
    (BadSet A q.val (T q)).card ≤
      2 ^ (k * k - 1225) * (Bn k q * 2 ^ T q * Y q * 2 ^ (1225 - CC q)) := by
  have h := card_BadSet A hloop hcomp q.val (T q) (ta q) (tb q) (ds q) (pos_ab q).1 (pos_ab q).2
    (tangent q)
  rw [CC_eq, Nat.choose_eq_descFactorial_div_factorial] at h
  have hc := CC_le q
  have hp : 2 ^ (k * k - CC q) = 2 ^ (k * k - 1225) * 2 ^ (1225 - CC q) := by
    rw [← pow_add]; congr 1; omega
  rw [hp] at h
  refine le_trans h (le_of_eq ?_)
  simp only [Bn, Y]
  ring

theorem main {k : ℕ} (hk : 1225 ≤ k * k)
    (hbud : ∑ q : Fin 5, Bn k q * 2 ^ T q * Y q * 2 ^ (1225 - CC q) < 2 ^ 1225)
    (A : Fin k → Fin k → Prop)
    (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i)) :
    ∃ label : Fin k → Fin k → Fin 2,
      ∀ q : Fin 5, ∀ I : Finset (Fin k),
      ∀ colors : Fin k → Fin 2,
        (∀ i ∈ I, (I.filter (fun j => A i j ∧ label i j ≠ colors j)).card ≤ q.val) →
        I.card < T q := by
  let Bad := (Finset.univ : Finset (Fin 5)).biUnion fun q => BadSet A q.val (T q)
  have hlt : Bad.card < (Finset.univ : Finset (Fin k → Fin k → Fin 2)).card := by
    calc Bad.card ≤ ∑ q : Fin 5, (BadSet A q.val (T q)).card := Finset.card_biUnion_le
      _ ≤ ∑ q : Fin 5, 2 ^ (k * k - 1225) * (Bn k q * 2 ^ T q * Y q * 2 ^ (1225 - CC q)) :=
          Finset.sum_le_sum fun q _ => bad_card hk A hloop hcomp q
      _ = 2 ^ (k * k - 1225) * ∑ q : Fin 5, Bn k q * 2 ^ T q * Y q * 2 ^ (1225 - CC q) := by
          rw [Finset.mul_sum]
      _ < 2 ^ (k * k - 1225) * 2 ^ 1225 :=
          Nat.mul_lt_mul_of_pos_left hbud (by positivity)
      _ = _ := by
          rw [← pow_add, Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, ← pow_mul, Nat.sub_add_cancel hk]
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨a, fun q I colors h => ?_⟩
  by_contra hn
  apply ha
  exact Finset.mem_biUnion.2 ⟨q, Finset.mem_univ _, mem_BadSet A a q.val (T q) I colors h
    (by omega)⟩

end SLSol

theorem solution (A : Fin 12607 → Fin 12607 → Prop)
    (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i)) :
    ∃ label : Fin 12607 → Fin 12607 → Fin 2,
      ∀ q : Fin 5, ∀ I : Finset (Fin 12607),
      ∀ colors : Fin 12607 → Fin 2,
        (∀ i ∈ I, (I.filter (fun j => A i j ∧ label i j ≠ colors j)).card ≤ q.val) →
        I.card < (![24,31,38,44,50] q) :=
  SLSol.main (by norm_num) SLSol.budget A hloop hcomp
