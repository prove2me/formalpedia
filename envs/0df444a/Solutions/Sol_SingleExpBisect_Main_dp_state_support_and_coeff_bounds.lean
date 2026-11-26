-- Prove2me | solution 1 for SingleExpBisect.Main.dp_state_support_and_coeff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:17:57.653797+00:00
-- url     : https://prove2.me/submissions/6b7e24f4-cb12-4aff-aa1b-75fa44841479

import Mathlib
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_SingleExpBisect_Main_NodeData
open scoped Classical
open SingleExpBisect.Main MinBisectFPT
set_option autoImplicit false

private def supportedOn {σ : Type} (P : (σ →₀ ℕ) → Prop) (F : MvPowerSeries σ ℚ) : Prop :=
  ∀ m, MvPowerSeries.coeff m F ≠ 0 → P m

private lemma supported_one {σ : Type} {P : (σ →₀ ℕ) → Prop} (h0 : P 0) :
    supportedOn P 1 := by
  classical
  intro m hm
  by_cases he : m = 0
  · simpa [he] using h0
  · simp [MvPowerSeries.coeff_one, he] at hm

private lemma supported_mul {σ : Type} {P : (σ →₀ ℕ) → Prop}
    (hadd : ∀ x y, P x → P y → P (x+y)) {F H : MvPowerSeries σ ℚ}
    (hf : supportedOn P F) (hh : supportedOn P H) : supportedOn P (F*H) := by
  classical
  intro m hm
  rw [MvPowerSeries.coeff_mul] at hm
  obtain ⟨⟨i,j⟩,hij,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hij]
  exact hadd i j (hf i (left_ne_zero_of_mul hn)) (hh j (right_ne_zero_of_mul hn))

private lemma supported_pow {σ : Type} {P : (σ →₀ ℕ) → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x+y)) {F : MvPowerSeries σ ℚ}
    (hf : supportedOn P F) (j : ℕ) : supportedOn P (F^j) := by
  induction j with
  | zero => simpa using supported_one h0
  | succ j ih => rw [pow_succ]; exact supported_mul hadd ih hf

private lemma supported_log {σ : Type} {P : (σ →₀ ℕ) → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x+y)) {F : MvPowerSeries σ ℚ}
    (hf : supportedOn P F) : supportedOn P (logPS F) := by
  classical
  intro m hm
  change (∑ j ∈ Finset.Icc 1 (Finsupp.degree m), ((-1 : ℚ) ^ (j+1) / (j:ℚ)) *
    MvPowerSeries.coeff m ((F-1)^j)) ≠ 0 at hm
  obtain ⟨j,hj,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  apply supported_pow h0 hadd (F := F-1) _ j m (right_ne_zero_of_mul hn)
  intro e he
  by_cases heq : e=0
  · simpa only [heq] using h0
  · apply hf e
    simpa [MvPowerSeries.coeff_one,heq] using he

private lemma no_prime {n : ℕ} (G : SimpleGraph (Fin n)) (W B : Finset (Fin n)) (k : ℕ) :
    supportedOn (fun e : Var n →₀ ℕ => e .x' = 0) (logPS (Zle G W B k : MvPowerSeries (Var n) ℚ)) := by
  apply supported_log (P := fun e : Var n →₀ ℕ => e .x' = 0) (by rfl) (fun e f he hf => by simp [he,hf])
  intro e he
  change MvPolynomial.coeff e (Zle G W B k) ≠ 0 at he
  rw [Zle,MvPolynomial.coeff_sum] at he
  obtain ⟨A,hA,hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  have eq : Finsupp.single Var.w (mu G W A) + yMono A = e := by
    by_contra h;simp [MvPolynomial.coeff_monomial,h] at hn
  rw [←eq];simp [yMono,Finsupp.finsetSum_apply]

private lemma ren_coords {n : ℕ} (B : Finset (Fin n)) (f : Var n →₀ ℕ) :
    (Finsupp.mapDomain (omegaVar B) f) .x' = f .x' ∧
    ∀ v, (Finsupp.mapDomain (omegaVar B) f) (.y v) = if v ∈ B then f (.y v) else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [Finsupp.mapDomain_add,Finsupp.add_apply,hf.1,hg.1,hf.2,hg.2,true_and]
    intro v;split <;> simp
  | single i j =>
    rw [Finsupp.mapDomain_single]
    cases i with
    | y u =>
        by_cases h : u ∈ B <;> simp [omegaVar,h,Finsupp.single_apply]
        · intro v; by_cases he : u = v <;> by_cases hv : v ∈ B <;> simp_all
        · intro v; by_cases he : u = v <;> by_cases hv : v ∈ B <;> simp_all
    | w => simp [omegaVar]
    | x => simp [omegaVar]
    | x' => simp [omegaVar]

private lemma rename_origin {σ τ : Type} [Finite σ] (f : σ → τ)
    (F : MvPowerSeries σ ℚ) (e : τ →₀ ℕ) (hn : MvPowerSeries.coeff e (renamePS f F) ≠ 0) :
    ∃ m : σ →₀ ℕ, Finsupp.mapDomain f m = e ∧ MvPowerSeries.coeff m F ≠ 0 := by
  classical
  by_contra! he;apply hn
  change (∑ᶠ (m : σ →₀ ℕ) (_ : Finsupp.mapDomain f m = e), MvPowerSeries.coeff m F) = 0
  have term (m : σ →₀ ℕ) : (∑ᶠ (_ : Finsupp.mapDomain f m = e), MvPowerSeries.coeff m F) = 0 := by
    by_cases hm : Finsupp.mapDomain f m = e
    · simp [he m hm]
    · simp [hm]
  simp [term]

private lemma discard_coeff {σ : Type} (U : Set (σ →₀ ℕ)) (F : MvPowerSeries σ ℚ) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (discard U F) = if e ∈ U then 0 else MvPowerSeries.coeff e F := rfl

private lemma log_coords {n : ℕ} (G : SimpleGraph (Fin n)) (W B S : Finset (Fin n)) (k : ℕ)
    {e : Var n →₀ ℕ} (hn : MvPowerSeries.coeff e
      (truncKNB k n B (renamePS (omegaVar B) (LtS G W B k S))) ≠ 0) :
    e .x' = 0 ∧ (∀ v ∉ S, e (.y v) = 0) ∧ e .x ≤ n ∧ e .w ≤ k ∧ ∑ v ∈ B,e (.y v) ≤ 2*k := by
  classical
  rw [truncKNB,discard_coeff] at hn
  split at hn
  · contradiction
  rename_i hb
  simp only [Set.mem_setOf_eq,not_not] at hb
  obtain ⟨m,hm,hF⟩ := rename_origin _ _ _ hn
  rw [LtS,discard_coeff] at hF
  split at hF
  · contradiction
  rename_i hs'
  simp only [Set.mem_setOf_eq,not_not] at hs'
  obtain ⟨hp,hy⟩ := ren_coords B m
  rw [hm] at hp hy
  refine ⟨hp.trans (no_prime G W B k m hF),?_,hb.2.1,hb.1,hb.2.2⟩
  intro v hv
  rw [hy]
  by_cases h : v ∈ B
  · rw [if_pos h]
    by_contra! hh
    exact hv (hs' ▸ Finset.mem_filter.mpr ⟨h,Nat.pos_of_ne_zero hh⟩)
  · rw [if_neg h]

private lemma histogram {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℕ) (d : ℕ)
    (hd : ∑ i, f i ≤ d) : ∃ m : Sym (Option α) d, ∀ i, m.val.count (some i) = f i := by
  classical
  let x : Multiset (Option α) := ∑ i, Multiset.replicate (f i) (some i)
  have sz : x.card = ∑ i, f i := by simp [x,Multiset.card_sum]
  let z := x + Multiset.replicate (d - x.card) none
  have hz : z.card = d := by simp [z,sz,Nat.add_sub_of_le hd]
  refine ⟨⟨z,hz⟩,?_⟩
  intro i
  simp [z,x,Multiset.count_sum',Multiset.count_replicate,eq_comm]

private theorem logCount {n : ℕ} (G : SimpleGraph (Fin n)) (W B S : Finset (Fin n)) (k : ℕ)
    (hS : S ⊆ B) (hsize : S.card ≤ 2*k) :
    ∃ E : Finset (Var n →₀ ℕ), E.card ≤ (n+1)*(k+1)*2^(4*k) ∧
      ∀ e, MvPowerSeries.coeff e (truncKNB k n B (renamePS (omegaVar B) (LtS G W B k S))) ≠ 0 → e ∈ E := by
  classical
  let M := Sym (Option (↑S)) (2*k)
  let V := fun (m : M) => ∑ j : ↑S, Finsupp.single (Var.y j.val) (m.val.count (some j))
  let f := fun p : Fin (n+1) × Fin (k+1) × M =>
    Finsupp.single Var.x p.1.val + Finsupp.single Var.w p.2.1.val + V p.2.2
  let E := Finset.univ.image f
  have hM : Fintype.card M ≤ 2^(4*k) := by
    rw [show Fintype.card M = _ from Sym.card_sym_eq_choose (2*k)]
    simp only [Fintype.card_option,Fintype.card_coe]
    exact (Nat.choose_le_two_pow ..).trans (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨E,?_,?_⟩
  · calc
      _ ≤ (Finset.univ : Finset (Fin (n+1) × Fin (k+1) × M)).card := Finset.card_image_le
      _ = (n+1)*(k+1)*Fintype.card M := by simp [mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_left _ hM
  · intro e hn
    obtain ⟨hprime,hy,hx,hw,hs⟩ := log_coords G W B S k hn
    have hs' : ∑ v : ↑S,e (.y v.val) ≤ 2*k := by
      rw [Finset.sum_coe_sort S (fun v : Fin n => e (.y v))]
      exact (Finset.sum_le_sum_of_subset_of_nonneg hS (by intros;omega)).trans hs
    obtain ⟨m,hm⟩ := histogram (fun v : ↑S => e (.y v.val)) (2*k) hs'
    apply Finset.mem_image.mpr
    refine ⟨(⟨e .x,Nat.lt_succ_of_le hx⟩,⟨e .w,Nat.lt_succ_of_le hw⟩,m),Finset.mem_univ _,?_⟩
    ext z
    cases z with
    | x => simp [f,V,Finsupp.finsetSum_apply]
    | w => simp [f,V,Finsupp.finsetSum_apply]
    | x' => simp [f,V,Finsupp.finsetSum_apply,hprime]
    | y v =>
      simp only [f,V,Finsupp.add_apply,Finsupp.finsetSum_apply,hm,Finsupp.single_apply]
      by_cases hv : v ∈ S
      · let i : ↑S := ⟨v,hv⟩
        have hsum : (∑ j : ↑S, if Var.y j.val = Var.y v then e (.y j.val) else 0) = e (.y v) := by
          rw [Finset.sum_eq_single i]
          · simp [i]
          · intro j _ hji;have hne : j.val ≠ v := fun h => hji (Subtype.ext h);simp [hne]
          · simp
        simpa [eq_comm] using hsum
      · have hsum : (∑ j : ↑S, if Var.y j.val = Var.y v then e (.y j.val) else 0) = 0 := by
          apply Finset.sum_eq_zero;intro j _
          have hne : j.val ≠ v := fun h => hv (h ▸ j.property)
          simp [hne]
        simpa [hy v hv,eq_comm] using hsum

private lemma rename_exponent {n : ℕ} (D A : Finset (Fin n)) (c : ℕ) :
    Finsupp.mapDomain (omegaVar D) (Finsupp.single Var.w c + yMono A) =
      Finsupp.single Var.x (A \ D).card + Finsupp.single Var.w c + yMono (A ∩ D) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [yMono,omegaVar,Finsupp.mapDomain_single]
  | insert i A hi ih =>
    have hs : yMono (insert i A) = Finsupp.single (Var.y i) 1 + yMono A := by simp [yMono,hi]
    rw [hs,add_left_comm,Finsupp.mapDomain_add,Finsupp.mapDomain_single,ih]
    by_cases hd : i ∈ D
    · have e : insert i A \ D = A \ D := by ext x; simp only [Finset.mem_sdiff,Finset.mem_insert]; constructor <;> aesop
      have f : insert i A ∩ D = insert i (A ∩ D) := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; constructor <;> aesop
      rw [e,f]; simp [omegaVar,hd,yMono,hi,add_comm,add_left_comm,add_assoc]
    · have e : insert i A \ D = insert i (A \ D) := by ext x; simp only [Finset.mem_sdiff,Finset.mem_insert]; constructor <;> aesop
      have f : insert i A ∩ D = A ∩ D := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; constructor <;> aesop
      rw [e,f,Finset.card_insert_of_notMem (by simp [hi]),Finsupp.single_add]
      simp only [omegaVar,if_neg hd]; abel

private lemma renamed_cut_support {n : ℕ} (G : SimpleGraph (Fin n)) (W D : Finset (Fin n)) (k : ℕ)
    (A : Finset (Finset (Fin n))) (hk : ∀ S ∈ A, mu G W S ≤ k) :
    let P := omega D (∑ S ∈ A, MvPolynomial.monomial (Finsupp.single Var.w (mu G W S) + yMono S) 1)
    P.support.card ≤ 2^D.card * (n+1) * (k+1) ∧
      ∀ e, ∃ j : ℕ, j ≤ 2^n ∧ MvPolynomial.coeff e P = (j : ℚ) := by
  classical
  dsimp only
  let exp := fun S : Finset (Fin n) => Finsupp.single Var.x (S \ D).card +
    Finsupp.single Var.w (mu G W S) + yMono (S ∩ D)
  let P := ∑ S ∈ A, MvPolynomial.monomial (exp S) (1:ℚ)
  have eq : omega D (∑ S ∈ A, MvPolynomial.monomial (Finsupp.single Var.w (mu G W S) + yMono S) 1) = P := by
    rw [map_sum]; apply Finset.sum_congr rfl;intro S hS
    change MvPolynomial.rename (omegaVar D) _ = _
    rw [MvPolynomial.rename_monomial,rename_exponent]
  rw [eq]
  let pack := D.powerset ×ˢ (Finset.range (n+1) ×ˢ Finset.range (k+1))
  let mono := fun p : Finset (Fin n) × (ℕ × ℕ) =>
    Finsupp.single Var.x p.2.1 + Finsupp.single Var.w p.2.2 + yMono p.1
  have hc (e : Var n →₀ ℕ) : MvPolynomial.coeff e P = ((A.filter (fun S => exp S = e)).card : ℚ) := by
    simp only [P,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
    simp [Finset.sum_boole,eq_comm]
  constructor
  · have hs : P.support ⊆ pack.image mono := by
      intro e he
      have hn := MvPolynomial.mem_support_iff.mp he
      rw [hc] at hn
      obtain ⟨S,hS⟩ := Finset.card_pos.mp (by exact_mod_cast (show 0 < (((A.filter (fun S => exp S=e)).card):ℚ) by positivity))
      obtain ⟨hA,heq⟩ := Finset.mem_filter.mp hS
      refine Finset.mem_image.mpr ⟨(S ∩ D,(S \ D).card,mu G W S),?_,heq⟩
      apply Finset.mem_product.mpr;refine ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,Finset.mem_product.mpr ⟨?_,?_⟩⟩
      · apply Finset.mem_range.mpr
        have h : (S \ D).card ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
        exact Nat.lt_succ_of_le h
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hk S hA))
    have h := (Finset.card_le_card hs).trans Finset.card_image_le
    simpa [pack,mul_assoc] using h
  · intro e
    refine ⟨_,?_,hc e⟩
    have hb := (Finset.card_le_card (Finset.filter_subset (fun S => exp S=e) A)).trans (Finset.card_le_univ _)
    simpa using hb

private theorem polyCount {n : ℕ} (G : SimpleGraph (Fin n)) (W B D : Finset (Fin n)) (k : ℕ) :
    ∀ P ∈ ({omega D (Zfull G W k), omega D (Zle G W B k)} : Finset (MvPolynomial (Var n) ℚ)),
      P.support.card ≤ 2^D.card * (n+1) * (k+1) ∧
      ∀ e, ∃ j : ℕ, j ≤ 2^n ∧ MvPolynomial.coeff e P = (j : ℚ) := by
  intro P hP
  simp only [Finset.mem_insert,Finset.mem_singleton] at hP
  rcases hP with rfl | rfl
  · exact renamed_cut_support G W D k _ (fun _ h => (Finset.mem_filter.mp h).2)
  · exact renamed_cut_support G W D k _ (fun _ h => (Finset.mem_filter.mp h).2.1)

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (W B D : Finset (Fin n)) (k : ℕ) :
    (∀ P ∈ ({omega D (Zfull G W k), omega D (Zle G W B k)} : Finset (MvPolynomial (Var n) ℚ)),
      P.support.card ≤ 2^D.card * (n+1) * (k+1) ∧
      ∀ e, ∃ j : ℕ, j ≤ 2^n ∧ MvPolynomial.coeff e P = (j : ℚ)) ∧
    ∀ S ⊆ B, S.card ≤ 2*k →
      ∃ E : Finset (Var n →₀ ℕ), E.card ≤ (n+1)*(k+1)*2^(4*k) ∧
        ∀ e, MvPowerSeries.coeff e (truncKNB k n B (renamePS (omegaVar B) (LtS G W B k S))) ≠ 0 → e ∈ E := by
  exact ⟨polyCount G W B D k,fun S hS hk => logCount G W B S k hS hk⟩
