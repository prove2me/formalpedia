-- Prove2me | solution 1 for TradingNetFlow.ChainStable.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:57:46.682257+00:00
-- url     : https://prove2.me/submissions/9e09f1e5-a19a-4258-b8ab-c537b0f78e71
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TradingNetFlow_ChainStable_Model
import Theorems.Thm_DiscreteConvex_MConvexFunctions_mnat_convex_iff_exchange_axiom
import Theorems.Thm_SteinitzExchange_Duality_mconcave_intersection_optimality

open Finset TradingNetFlow.ChainStable SteinitzExchange.Duality

namespace TNF41

/-! ### Negation `WithBot ℝ → WithTop ℝ` -/

noncomputable def negWT (a : WithBot ℝ) : WithTop ℝ :=
  WithBot.recBotCoe ⊤ (fun r => ((-r : ℝ) : WithTop ℝ)) a

@[simp] lemma negWT_bot : negWT ⊥ = ⊤ := rfl
@[simp] lemma negWT_coe (r : ℝ) : negWT (r : WithBot ℝ) = ((-r : ℝ) : WithTop ℝ) := rfl

lemma negWT_add (a b : WithBot ℝ) : negWT (a + b) = negWT a + negWT b := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp
    | coe b =>
      rw [← WithBot.coe_add, negWT_coe, negWT_coe, negWT_coe, ← WithTop.coe_add, neg_add]

lemma negWT_anti : Antitone negWT := by
  intro a b h
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe b =>
      simp only [negWT_coe]
      exact WithTop.coe_le_coe.2 (neg_le_neg (WithBot.coe_le_coe.1 h))

lemma negWT_sup {ι : Type*} (s : Finset ι) (f : ι → WithBot ℝ) :
    negWT (s.sup f) = s.inf (fun j => negWT (f j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sup_insert, inf_insert, ← ih]
    exact negWT_anti.map_max

lemma negWT_ne_top {a : WithBot ℝ} : negWT a ≠ ⊤ ↔ a ≠ ⊥ := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe a => simp

/-- An M♮-concave function, negated, satisfies (M♮-EXC[Z]). -/
lemma mnatExch_of_concave {K : Type*} [Fintype K] [DecidableEq K] (U : (K → ℤ) → WithBot ℝ)
    (hU : DiscreteConvex.EconomicEquilibrium.MNaturalConcave U) :
    DiscreteConvex.MConvexFunctions.MNatExchangeAxiom (fun x => negWT (U x)) := by
  intro x hx y hy u hu
  have hx' : U x ≠ ⊥ := negWT_ne_top.1 hx
  have hy' : U y ≠ ⊥ := negWT_ne_top.1 hy
  have key := hU.2 x hx' y hy' u hu
  have := negWT_anti key
  rw [negWT_add, negWT_anti.map_max, negWT_add, negWT_sup] at this
  simpa only [negWT_add] using this

/-! ### Base sets -/

lemma baseSet_of_exc {V : Type*} [DecidableEq V] (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ)
    (h : SatisfiesEXC B ω) (hne : B.Nonempty) : IsIntegralBaseSet B := by
  refine ⟨hne, fun x hx y hy u hu => ?_⟩
  obtain ⟨v, hv, h1, -, -⟩ := h x hx y hy u hu
  exact ⟨v, hv, h1⟩

lemma pairing_exch {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (y : V → ℤ) (u v : V) :
    pairing p (toReal (y - chi u + chi v)) = pairing p (toReal y) - p u + p v := by
  simp only [pairing, toReal, chi, Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub,
    mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, Pi.single_apply]
  simp

/-- Integer vectors in a box `[-K, K]^V` whose sum over each class of `cls` vanishes. -/
noncomputable def classSet {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C] [Fintype C]
    (cls : V → C) (K : ℤ) : Finset (V → ℤ) :=
  (Fintype.piFinset fun _ : V => Icc (-K) K).filter
    (fun z => ∀ c, ∑ v ∈ univ.filter (fun v => cls v = c), z v = 0)

lemma mem_classSet {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C] [Fintype C]
    (cls : V → C) (K : ℤ) (z : V → ℤ) :
    z ∈ classSet cls K ↔ (∀ v, -K ≤ z v ∧ z v ≤ K) ∧
      ∀ c, ∑ v ∈ univ.filter (fun v => cls v = c), z v = 0 := by
  simp [classSet, Fintype.mem_piFinset]

lemma classSet_exc {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C] [Fintype C]
    (cls : V → C) (K : ℤ) : SatisfiesEXC (classSet cls K) (fun _ => 0) := by
  intro x hx y hy u hu
  rw [mem_classSet] at hx hy
  -- some coordinate in the class of `u` decreases
  have hex : ∃ v, cls v = cls u ∧ x v < y v := by
    by_contra hc
    push Not at hc
    have hlt : ∑ v ∈ univ.filter (fun v => cls v = cls u), y v
        < ∑ v ∈ univ.filter (fun v => cls v = cls u), x v :=
      Finset.sum_lt_sum (fun v hv => hc v (mem_filter.1 hv).2)
        ⟨u, mem_filter.2 ⟨mem_univ _, rfl⟩, by simpa [Pi.sub_apply] using hu⟩
    rw [hx.2, hy.2] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨v, hvc, hv⟩ := hex
  have huv : u ≠ v := by
    rintro rfl; simp [Pi.sub_apply] at hu; omega
  refine ⟨v, by simp [Pi.sub_apply]; omega, ?_, ?_, by simp⟩
  · rw [mem_classSet]
    refine ⟨fun w => ?_, fun c => ?_⟩
    · have := hx.1 w; have h1 := hy.1 u; have h2 := hy.1 v
      simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply]
      simp only [Pi.sub_apply] at hu
      by_cases hwu : w = u
      · subst hwu; simp [huv]; omega
      · by_cases hwv : w = v
        · subst hwv; simp [hwu]; omega
        · simp [hwu, hwv]; omega
    · simp only [Pi.add_apply, Pi.sub_apply, sum_add_distrib, sum_sub_distrib, hx.2 c, chi]
      rw [Finset.sum_pi_single', Finset.sum_pi_single']
      simp only [mem_filter, mem_univ, true_and]
      by_cases hc : cls u = c
      · rw [if_pos hc, if_pos (hvc.trans hc)]; ring
      · rw [if_neg hc, if_neg (fun h => hc (hvc.symm.trans h))]; ring
  · rw [mem_classSet]
    refine ⟨fun w => ?_, fun c => ?_⟩
    · have := hy.1 w; have h1 := hx.1 u; have h2 := hx.1 v
      simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply]
      simp only [Pi.sub_apply] at hu
      by_cases hwu : w = u
      · subst hwu; simp [huv]; omega
      · by_cases hwv : w = v
        · subst hwv; simp [hwu]; omega
        · simp [hwu, hwv]; omega
    · simp only [Pi.add_apply, Pi.sub_apply, sum_add_distrib, sum_sub_distrib, hy.2 c, chi]
      rw [Finset.sum_pi_single', Finset.sum_pi_single']
      simp only [mem_filter, mem_univ, true_and]
      by_cases hc : cls u = c
      · rw [if_pos hc, if_pos (hvc.trans hc)]; ring
      · rw [if_neg hc, if_neg (fun h => hc (hvc.symm.trans h))]; ring

/-! ### Block-separable functions on a sigma type -/

section Block
variable {N : Type*} [Fintype N] [DecidableEq N] {α : N → Type*} [∀ i, Fintype (α i)]
  [∀ i, DecidableEq (α i)]

def blk (z : (Σ i, α i) → ℤ) (i : N) : α i → ℤ := fun a => z ⟨i, a⟩

open Classical in
noncomputable def blockSet (L : (i : N) → (α i → ℤ) → WithTop ℝ) (K : ℤ) :
    Finset ((Σ i, α i) → ℤ) :=
  (Fintype.piFinset fun _ => Icc (-K) K).filter (fun z => ∀ i, L i (blk z i) ≠ ⊤)

lemma mem_blockSet (L : (i : N) → (α i → ℤ) → WithTop ℝ) (K : ℤ)
    (hK : ∀ i x, L i x ≠ ⊤ → ∀ a, -K ≤ x a ∧ x a ≤ K) (z : (Σ i, α i) → ℤ) :
    z ∈ blockSet L K ↔ ∀ i, L i (blk z i) ≠ ⊤ := by
  classical
  simp only [blockSet, mem_filter, Fintype.mem_piFinset, mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun v => ?_, h⟩
    obtain ⟨i, a⟩ := v
    exact hK i _ (h i) a

noncomputable def blockVal (L : (i : N) → (α i → ℤ) → WithTop ℝ) (z : (Σ i, α i) → ℤ) : ℝ :=
  ∑ i, -(WithTop.untopD 0 (L i (blk z i)))

lemma coe_untop {t : WithTop ℝ} (h : t ≠ ⊤) : ((WithTop.untopD 0 t : ℝ) : WithTop ℝ) = t := by
  obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.1 h
  simp

lemma blk_sub_add_self (x : (Σ i, α i) → ℤ) (i : N) (a b : α i) :
    blk (x - chi ⟨i, a⟩ + chi ⟨i, b⟩) i
      = fun w => blk x i w - DiscreteConvex.MConvexFunctions.CharVec a w
          + DiscreteConvex.MConvexFunctions.CharVec b w := by
  funext w
  simp [blk, chi, Pi.single_apply, DiscreteConvex.MConvexFunctions.CharVec]

lemma blk_add_sub_self (x : (Σ i, α i) → ℤ) (i : N) (a b : α i) :
    blk (x + chi ⟨i, a⟩ - chi ⟨i, b⟩) i
      = fun w => blk x i w + DiscreteConvex.MConvexFunctions.CharVec a w
          - DiscreteConvex.MConvexFunctions.CharVec b w := by
  funext w
  simp [blk, chi, Pi.single_apply, DiscreteConvex.MConvexFunctions.CharVec]

lemma blk_sub_add_ne (x : (Σ i, α i) → ℤ) {i j : N} (h : j ≠ i) (a b : α i) :
    blk (x - chi ⟨i, a⟩ + chi ⟨i, b⟩) j = blk x j := by
  funext w
  simp [blk, chi, Pi.single_apply, h]

lemma blk_add_sub_ne (x : (Σ i, α i) → ℤ) {i j : N} (h : j ≠ i) (a b : α i) :
    blk (x + chi ⟨i, a⟩ - chi ⟨i, b⟩) j = blk x j := by
  funext w
  simp [blk, chi, Pi.single_apply, h]

lemma blockSet_exc (L : (i : N) → (α i → ℤ) → WithTop ℝ) (K : ℤ)
    (hK : ∀ i x, L i x ≠ ⊤ → ∀ a, -K ≤ x a ∧ x a ≤ K)
    (hL : ∀ i, DiscreteConvex.MConvexFunctions.MExchangeAxiom (L i)) :
    SatisfiesEXC (blockSet L K) (blockVal L) := by
  intro x hx y hy u hu
  rw [mem_blockSet L K hK] at hx hy
  obtain ⟨i, a⟩ := u
  have ha : a ∈ DiscreteConvex.MConvexFunctions.SuppPos (blk x i) (blk y i) := by
    unfold DiscreteConvex.MConvexFunctions.SuppPos
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    show y ⟨i, a⟩ < x ⟨i, a⟩
    have := hu; rw [Pi.sub_apply] at this; omega
  obtain ⟨b, hb, hineq⟩ := hL i (blk x i) (hx i) (blk y i) (hy i) a ha
  have hb' : x ⟨i, b⟩ < y ⟨i, b⟩ := (mem_filter.1 hb).2
  have hlhs : L i (blk x i) + L i (blk y i) ≠ ⊤ := WithTop.add_ne_top.2 ⟨hx i, hy i⟩
  have hr := ne_top_of_le_ne_top hlhs hineq
  obtain ⟨hr1, hr2⟩ := WithTop.add_ne_top.1 hr
  refine ⟨⟨i, b⟩, by rw [Pi.sub_apply]; omega, ?_, ?_, ?_⟩
  · rw [mem_blockSet L K hK]
    intro j
    by_cases hj : j = i
    · subst hj; rw [blk_sub_add_self]; exact hr1
    · rw [blk_sub_add_ne x hj]; exact hx j
  · rw [mem_blockSet L K hK]
    intro j
    by_cases hj : j = i
    · subst hj; rw [blk_add_sub_self]; exact hr2
    · rw [blk_add_sub_ne y hj]; exact hy j
  · unfold blockVal
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_le_sum (fun j _ => ?_)
    by_cases hj : j = i
    · subst hj
      rw [blk_sub_add_self, blk_add_sub_self]
      rw [← coe_untop (hx j), ← coe_untop (hy j), ← coe_untop hr1, ← coe_untop hr2,
        ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at hineq
      linarith
    · rw [blk_sub_add_ne x hj, blk_add_sub_ne y hj]

end Block

lemma classSet_shift {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C] [Fintype C]
    (cls : V → C) (K : ℤ) (z : V → ℤ) (hz : z ∈ classSet cls (K + 1))
    (hb : ∀ w, -K ≤ z w ∧ z w ≤ K) (u v : V) (huv : cls u = cls v) :
    z - chi u + chi v ∈ classSet cls (K + 1) := by
  rw [mem_classSet] at hz ⊢
  refine ⟨fun w => ?_, fun c => ?_⟩
  · have := hb w
    simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply]
    split_ifs <;> omega
  · simp only [Pi.add_apply, Pi.sub_apply, sum_add_distrib, sum_sub_distrib, hz.2 c, chi]
    rw [Finset.sum_pi_single', Finset.sum_pi_single']
    simp only [mem_filter, mem_univ, true_and]
    by_cases hc : cls u = c
    · rw [if_pos hc, if_pos (huv.symm.trans hc)]; ring
    · rw [if_neg hc, if_neg (fun h => hc (huv.trans h))]; ring

section Econ
variable {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]

/-- Agent `i`'s negated valuation, lifted to `ℤ^{\{0\} ∪ δ(i)}` (Murota, Eq. (6.4)). -/
noncomputable def Lf (G : Economy N E) (i : N) : (Option {e // e ∈ G.delta i} → ℤ) → WithTop ℝ :=
  DiscreteConvex.MConvexFunctions.LiftedFunction (fun x => negWT (G.wSigned i x))

def setOf' (G : Economy N E) (i : N) (y : {e // e ∈ G.delta i} → ℤ) : Finset E :=
  (univ.filter (fun e => y e ≠ 0)).map (Function.Embedding.subtype _)

lemma sign_cases (G : Economy N E) (i : N) (e : E) : G.sign i e = 1 ∨ G.sign i e = -1 := by
  unfold Economy.sign; split_ifs <;> simp

lemma Lf_ne_top (G : Economy N E) (i : N) (x : Option {e // e ∈ G.delta i} → ℤ) :
    Lf G i x ≠ ⊤ ↔ (x none = -(∑ e, x (some e))) ∧
      ∀ e, x (some e) = 0 ∨ x (some e) = G.sign i e.1 := by
  unfold Lf DiscreteConvex.MConvexFunctions.LiftedFunction
  by_cases h : x none = -(∑ e, x (some e))
  · rw [if_pos h, negWT_ne_top]
    unfold Economy.wSigned
    beta_reduce
    by_cases hb : ∀ e, x (some e) = 0 ∨ x (some e) = G.sign i e.1
    · rw [if_pos hb]; simp [h, hb]
    · rw [if_neg hb]
      simp only [ne_eq, not_true_eq_false, false_iff, not_and]
      exact fun _ h' => hb h'
  · rw [if_neg h]
    simp only [ne_eq, not_true_eq_false, false_iff, not_and]
    exact fun h' => absurd h' h

lemma Lf_val (G : Economy N E) (i : N) (x : Option {e // e ∈ G.delta i} → ℤ)
    (h : Lf G i x ≠ ⊤) :
    WithTop.untopD 0 (Lf G i x) = -G.w i (setOf' G i (fun e => x (some e))) := by
  obtain ⟨h1, h2⟩ := (Lf_ne_top G i x).1 h
  unfold Lf DiscreteConvex.MConvexFunctions.LiftedFunction
  rw [if_pos h1]
  unfold Economy.wSigned
  beta_reduce
  rw [if_pos h2, negWT_coe, WithTop.untopD_coe]
  rfl

lemma Lf_bound (G : Economy N E) (i : N) (x : Option {e // e ∈ G.delta i} → ℤ)
    (h : Lf G i x ≠ ⊤) : ∀ a, -((Fintype.card E : ℤ) + 1) ≤ x a ∧ x a ≤ (Fintype.card E : ℤ) + 1 := by
  obtain ⟨h1, h2⟩ := (Lf_ne_top G i x).1 h
  have hs1 : ∀ e, |x (some e)| ≤ 1 := by
    intro e
    rcases h2 e with h | h
    · rw [h]; simp
    · rw [h]; rcases sign_cases G i e.1 with hs | hs <;> rw [hs] <;> simp
  intro a
  cases a with
  | some e => have := hs1 e; rw [abs_le] at this; omega
  | none =>
    have hsum : |∑ e, x (some e)| ≤ (Fintype.card E : ℤ) := by
      calc |∑ e, x (some e)| ≤ ∑ e, |x (some e)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _e : {e // e ∈ G.delta i}, (1 : ℤ) := sum_le_sum (fun e _ => hs1 e)
        _ = Fintype.card {e // e ∈ G.delta i} := by simp
        _ ≤ Fintype.card E := by exact_mod_cast Fintype.card_subtype_le _
    rw [h1]
    rw [abs_le] at hsum
    omega

/-- The lifted signed characteristic vector of a set `S` of trades of agent `i`. -/
def liftv (G : Economy N E) (i : N) (S : Finset E) : Option {e // e ∈ G.delta i} → ℤ
  | none => -(∑ e : {e // e ∈ G.delta i}, if e.1 ∈ S then G.sign i e.1 else 0)
  | some e => if e.1 ∈ S then G.sign i e.1 else 0

lemma liftv_fin (G : Economy N E) (i : N) (S : Finset E) : Lf G i (liftv G i S) ≠ ⊤ := by
  rw [Lf_ne_top]
  refine ⟨rfl, fun e => ?_⟩
  simp only [liftv]
  split_ifs <;> simp

lemma liftv_set (G : Economy N E) (i : N) (S : Finset E) (hS : S ⊆ G.delta i) :
    setOf' G i (fun e => liftv G i S (some e)) = S := by
  ext x
  unfold setOf'
  rw [mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [mem_filter] at he
    by_contra hx
    apply he.2
    show liftv G i S (some e) = 0
    simp only [liftv]
    exact if_neg hx
  · intro hx
    refine ⟨⟨x, hS hx⟩, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    show liftv G i S (some ⟨x, hS hx⟩) ≠ 0
    simp only [liftv]
    rw [if_pos hx]
    rcases sign_cases G i x with h | h <;> rw [h] <;> simp

lemma mem_delta_iff (G : Economy N E) (i : N) (e : E) :
    e ∈ G.delta i ↔ G.seller e = i ∨ G.buyer e = i := by
  simp [Economy.delta, Economy.deltaOut, Economy.deltaIn]

lemma utility_eq_signed (G : Economy N E) (hsb : ∀ e, G.seller e ≠ G.buyer e) (i : N)
    (S : Finset E) (hS : S ⊆ G.delta i) (q : E → ℝ) :
    G.utility i S q = G.w i S +
      ∑ e : {e // e ∈ G.delta i}, q e.1 * ((if e.1 ∈ S then G.sign i e.1 else 0 : ℤ) : ℝ) := by
  unfold Economy.utility
  rw [Finset.sum_coe_sort (G.delta i) (fun e => q e * ((if e ∈ S then G.sign i e else 0 : ℤ) : ℝ))]
  have hout : S ∩ G.deltaOut i = (G.delta i).filter (fun e => e ∈ S ∧ G.seller e = i) := by
    ext e
    simp only [mem_inter, mem_filter, Economy.deltaOut, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hS h1, h1, h2⟩
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  have hin : S ∩ G.deltaIn i = (G.delta i).filter (fun e => e ∈ S ∧ G.buyer e = i) := by
    ext e
    simp only [mem_inter, mem_filter, Economy.deltaIn, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hS h1, h1, h2⟩
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  rw [hout, hin, sum_filter, sum_filter, add_sub_assoc, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl (fun e he => ?_)
  rw [mem_delta_iff] at he
  by_cases heS : e ∈ S
  · by_cases hse : G.seller e = i
    · have hbe : G.buyer e ≠ i := fun h => hsb e (hse.trans h.symm)
      simp [heS, hse, hbe, Economy.sign]
    · have hbe : G.buyer e = i := he.resolve_left hse
      simp [heS, hse, hbe, Economy.sign]
  · simp [heS]

end Econ

end TNF41

open TNF41 DiscreteConvex.MConvexFunctions in
theorem solution {N E : Type*} [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E]
    (G : Economy N E) (hG : G.Standing) :
    ∃ (X : Finset E) (p : E → ℝ), G.IsCompetitiveEquilibrium X p := by
  classical
  rcases isEmpty_or_nonempty N with hN | hN
  · exact ⟨∅, 0, fun i => (IsEmpty.false i).elim⟩
  have hsb := hG.1
  set K : ℤ := (Fintype.card E : ℤ) + 1 with hK
  have hKb : ∀ i x, Lf G i x ≠ ⊤ → ∀ a, -K ≤ x a ∧ x a ≤ K := fun i x h => Lf_bound G i x h
  -- agents' lifted valuations are M-concave (Murota, Theorem 6.2)
  have hL : ∀ i, MExchangeAxiom (Lf G i) := by
    intro i
    have hne : (DomZ (fun x => negWT (G.wSigned i x))).Nonempty := by
      refine ⟨0, ?_⟩
      show negWT (G.wSigned i 0) ≠ ⊤
      rw [negWT_ne_top]
      unfold Economy.wSigned
      split_ifs with h0
      · exact WithBot.coe_ne_bot
      · exact absurd (fun e => Or.inl rfl) h0
    exact (mnat_convex_iff_exchange_axiom _ hne).2 (mnatExch_of_concave _ (hG.2 i))
  haveI : Nonempty (Σ i : N, Option {e // e ∈ G.delta i}) :=
    ⟨⟨Classical.arbitrary N, none⟩⟩
  let cls : (Σ i : N, Option {e // e ∈ G.delta i}) → Option E := fun v => v.2.map Subtype.val
  set B1 := blockSet (Lf G) K with hB1
  set B2 := classSet cls (K + 1) with hB2
  set ω1 := blockVal (Lf G) with hω1
  have hB1exc : SatisfiesEXC B1 ω1 := blockSet_exc _ K hKb hL
  have hB2exc : SatisfiesEXC B2 (fun _ => 0) := classSet_exc cls (K + 1)
  have h0B1 : (0 : (Σ i : N, Option {e // e ∈ G.delta i}) → ℤ) ∈ B1 := by
    rw [mem_blockSet _ K hKb]
    intro i
    rw [Lf_ne_top]
    simp [blk]
  have hKpos : 0 ≤ K := by positivity
  have h0B2 : (0 : (Σ i : N, Option {e // e ∈ G.delta i}) → ℤ) ∈ B2 := by
    rw [mem_classSet]
    refine ⟨fun v => ⟨by simp; omega, by simp; omega⟩, fun c => by simp⟩
  obtain ⟨ys, hys, hmax⟩ := Finset.exists_max_image (B1 ∩ B2) ω1 ⟨0, mem_inter.2 ⟨h0B1, h0B2⟩⟩
  obtain ⟨hys1, hys2⟩ := mem_inter.1 hys
  obtain ⟨p, hp1, hp2⟩ := ((mconcave_intersection_optimality B1 B2
    (baseSet_of_exc _ _ hB1exc ⟨0, h0B1⟩) (baseSet_of_exc _ _ hB2exc ⟨0, h0B2⟩) ω1 (fun _ => 0)
    hB1exc hB2exc ys hys1 hys2).1).1
    (fun x hx1 hx2 => by simpa using hmax x (mem_inter.2 ⟨hx1, hx2⟩))
  have hysfin : ∀ i, Lf G i (blk ys i) ≠ ⊤ := (mem_blockSet _ K hKb ys).1 hys1
  have hysb : ∀ w, -K ≤ ys w ∧ ys w ≤ K := fun w => hKb w.1 _ (hysfin w.1) w.2
  -- potentials are constant on classes
  have hpeq : ∀ u v, cls u = cls v → p u = p v := by
    have hle : ∀ u v, cls u = cls v → p v ≤ p u := by
      intro u v huv
      have := hp2 _ (classSet_shift cls K ys hys2 hysb u v huv)
      simp only [perturb, pairing_exch] at this
      linarith
    exact fun u v h => le_antisymm (hle v u h.symm) (hle u v h)
  set c : ℝ := p ⟨Classical.arbitrary N, none⟩ with hc
  have hcn : ∀ i, p ⟨i, none⟩ = c := fun i => hpeq _ _ rfl
  have hs : ∀ e, e ∈ G.delta (G.seller e) := fun e => (mem_delta_iff G _ e).2 (Or.inl rfl)
  set q : E → ℝ := fun e => c - p ⟨G.seller e, some ⟨e, hs e⟩⟩ with hq
  have hpq : ∀ i (e : {e // e ∈ G.delta i}), p ⟨i, some e⟩ = c - q e.1 := by
    intro i e
    rw [hq]
    simp only
    rw [hpeq ⟨i, some e⟩ ⟨G.seller e.1, some ⟨e.1, hs e.1⟩⟩ rfl]
    ring
  -- the perturbed objective splits over agents
  let Ψ : (i : N) → (Option {e // e ∈ G.delta i} → ℤ) → ℝ := fun i x =>
    -(WithTop.untopD 0 (Lf G i x)) - ∑ a, p ⟨i, a⟩ * (x a : ℝ)
  have hpert : ∀ z, perturb ω1 (-p) z = ∑ i, Ψ i (blk z i) := by
    intro z
    simp only [perturb, pairing, toReal, hω1, blockVal, Ψ, blk, Pi.neg_apply]
    rw [Fintype.sum_sigma, ← sum_add_distrib]
    refine sum_congr rfl (fun i _ => ?_)
    simp only [neg_mul, sum_neg_distrib]
    ring
  -- agent `i`'s objective at a lifted set is its utility at prices `q`
  have hΨ : ∀ i (S : Finset E), S ⊆ G.delta i → Ψ i (liftv G i S) = G.utility i S q := by
    intro i S hS
    simp only [Ψ]
    rw [Lf_val G i _ (liftv_fin G i S), liftv_set G i S hS, utility_eq_signed G hsb i S hS q,
      Fintype.sum_option, hcn]
    simp only [liftv, hpq]
    push_cast
    simp only [sub_mul, sum_sub_distrib]
    rw [← mul_sum]
    ring
  -- the equilibrium outcome
  set X : Finset E := univ.filter (fun e => ys ⟨G.seller e, some ⟨e, hs e⟩⟩ ≠ 0) with hX
  have hcopy : ∀ (j : N) (e : E) (h : e ∈ G.delta j),
      ys ⟨j, some ⟨e, h⟩⟩ ≠ 0 ↔ e ∈ X := by
    intro j e h
    rw [hX, mem_filter]
    simp only [mem_univ, true_and]
    by_cases hj : G.seller e = j
    · subst hj; exact Iff.rfl
    · have hbj : G.buyer e = j := ((mem_delta_iff G j e).1 h).resolve_left hj
      subst hbj
      -- the class of `e` consists of its seller copy and its buyer copy
      set s : (Σ i : N, Option {e // e ∈ G.delta i}) := ⟨G.seller e, some ⟨e, hs e⟩⟩ with hsdef
      set b : (Σ i : N, Option {e // e ∈ G.delta i}) := ⟨G.buyer e, some ⟨e, h⟩⟩ with hbdef
      have hsb' : s ≠ b := fun hh => hsb e (congrArg Sigma.fst hh)
      have hfil : univ.filter (fun v => cls v = some e) = {s, b} := by
        ext v
        obtain ⟨k, a⟩ := v
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · intro hv
          cases a with
          | none => simp [cls] at hv
          | some e' =>
            obtain ⟨e', h'⟩ := e'
            simp only [cls, Option.map_some, Option.some.injEq] at hv
            subst hv
            rcases (mem_delta_iff G k e').1 h' with hk | hk
            · left; subst hk; rfl
            · right; subst hk; rfl
        · rintro (hv | hv)
          · rw [hv]; rfl
          · rw [hv]; rfl
      have hsum := (mem_classSet cls (K + 1) ys).1 hys2 |>.2 (some e)
      rw [hfil, sum_pair hsb'] at hsum
      constructor
      · intro hb0 hs0; apply hb0; change ys b = 0; omega
      · intro hs0 hb0; apply hs0; change ys s = 0; change ys b = 0 at hb0; omega
  have hblk : ∀ i, blk ys i = liftv G i (X ∩ G.delta i) := by
    intro i
    obtain ⟨h1, h2⟩ := (Lf_ne_top G i _).1 (hysfin i)
    have hsome : ∀ e : {e // e ∈ G.delta i}, blk ys i (some e) = liftv G i (X ∩ G.delta i) (some e) := by
      intro e
      simp only [liftv]
      have hiff := hcopy i e.1 e.2
      by_cases hx : e.1 ∈ X ∩ G.delta i
      · rw [if_pos hx]
        have hne : ys ⟨i, some e⟩ ≠ 0 := hiff.2 (mem_inter.1 hx).1
        rcases h2 e with h | h
        · exact absurd h hne
        · exact h
      · rw [if_neg hx]
        have : e.1 ∉ X := fun h' => hx (mem_inter.2 ⟨h', e.2⟩)
        by_contra hne
        exact this (hiff.1 hne)
    funext a
    cases a with
    | some e => exact hsome e
    | none =>
      rw [h1]
      simp only [liftv]
      congr 1
      exact sum_congr rfl (fun e _ => hsome e)
  refine ⟨X, q, fun i => ⟨by rw [univ_inter]; exact inter_subset_right, fun Y hY => ?_⟩⟩
  rw [univ_inter] at hY
  -- compare with the vector that replaces agent `i`'s block by `Y`
  let bl : (j : N) → Option {e // e ∈ G.delta j} → ℤ := Function.update (blk ys) i (liftv G i Y)
  let z : (Σ i : N, Option {e // e ∈ G.delta i}) → ℤ := fun v => bl v.1 v.2
  have hzb : ∀ j, blk z j = bl j := fun j => rfl
  have hz1 : z ∈ B1 := by
    rw [mem_blockSet _ K hKb]
    intro j
    rw [hzb]
    by_cases hj : j = i
    · subst hj; simp only [bl, Function.update_self]; exact liftv_fin G j Y
    · simp only [bl, Function.update_of_ne hj]; exact hysfin j
  have hopt := hp1 z hz1
  rw [hpert, hpert, ← Finset.add_sum_erase _ _ (mem_univ i),
    ← Finset.add_sum_erase _ _ (mem_univ i)] at hopt
  have hrest : ∑ j ∈ univ.erase i, Ψ j (blk z j) = ∑ j ∈ univ.erase i, Ψ j (blk ys j) := by
    refine sum_congr rfl (fun j hj => ?_)
    rw [hzb]
    simp only [bl, Function.update_of_ne (ne_of_mem_erase hj)]
  rw [hrest, hzb] at hopt
  simp only [bl, Function.update_self] at hopt
  rw [hblk i, hΨ i Y hY, hΨ i _ inter_subset_right] at hopt
  linarith
