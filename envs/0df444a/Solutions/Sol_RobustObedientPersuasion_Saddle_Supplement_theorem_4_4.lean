-- Prove2me | solution 1 for RobustObedientPersuasion.Saddle.Supplement.theorem_4_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:36:38.54864+00:00
-- url     : https://prove2.me/submissions/6816006b-1270-48d0-8be0-dfdb2a778995

import Mathlib
import Definitions.Def_RobustObedientPersuasion_Saddle_Model
import Definitions.Def_RobustObedientPersuasion_Saddle_Supplement_Unrestricted

section
namespace RobustObedientPersuasion.Saddle.Supplement.Dev
open RobustObedientPersuasion.Saddle RobustObedientPersuasion.Saddle.Supplement

section
variable {Ω A : Type*} [Fintype Ω] [Fintype A]

lemma le_one_of_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i)
    (h1 : ∑ i, f i = 1) (i : ι) : f i ≤ 1 := by
  rw [← h1]; exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

lemma alpha_sum (α : A → ℝ) (hα : α ∈ stdSimplex ℝ A) : ∑ a ∈ supp α, α a = 1 := by
  rw [← hα.2]
  unfold supp
  exact Finset.sum_filter_of_ne (fun a _ h => lt_of_le_of_ne (hα.1 a) (Ne.symm h))

lemma ident_mem {u : Ω → A → ℝ} {α : A → ℝ} (hα : α ∈ stdSimplex ℝ A) {μ : Ω → ℝ}
    (hμ : μ ∈ identifiedSet u α) : (∀ ω, 0 ≤ μ ω) ∧ ∑ ω, μ ω = 1 := by
  obtain ⟨ν, hν, hμ⟩ := hμ
  refine ⟨fun ω => ?_, ?_⟩
  · rw [hμ]
    exact Finset.sum_nonneg fun a ha => mul_nonneg (hα.1 a) ((hν a ha).1.1 ω)
  · simp_rw [hμ]
    rw [Finset.sum_comm]
    have : ∀ a ∈ supp α, ∑ ω, α a * ν a ω = α a := by
      intro a ha
      rw [← Finset.mul_sum, (hν a ha).1.2, mul_one]
    rw [Finset.sum_congr rfl this]
    exact alpha_sum α hα

lemma l1_le_two {p q : Ω → ℝ} (hp : (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1)
    (hq : (∀ ω, 0 ≤ q ω) ∧ ∑ ω, q ω = 1) : l1Dist p q ≤ 2 := by
  unfold l1Dist
  calc ∑ ω, |p ω - q ω| ≤ ∑ ω, (p ω + q ω) := Finset.sum_le_sum fun ω _ => by
        rw [abs_le]; constructor <;> linarith [hp.1 ω, hq.1 ω]
    _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num

lemma l1_nonneg (p q : Ω → ℝ) : 0 ≤ l1Dist p q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma rad_ge {u : Ω → A → ℝ} {α : A → ℝ} (hα : α ∈ stdSimplex ℝ A) {pbar p : Ω → ℝ}
    (hpbar : pbar ∈ identifiedSet u α) (hp : p ∈ identifiedSet u α) :
    l1Dist p pbar ≤ uncertaintyRadius u α pbar := by
  refine le_csSup ⟨2, ?_⟩ ⟨p, hp, rfl⟩
  rintro _ ⟨q, hq, rfl⟩
  exact l1_le_two (ident_mem hα hq) (ident_mem hα hpbar)

lemma rad_nonneg {u : Ω → A → ℝ} {α : A → ℝ} (hα : α ∈ stdSimplex ℝ A) {pbar : Ω → ℝ}
    (hpbar : pbar ∈ identifiedSet u α) : 0 ≤ uncertaintyRadius u α pbar :=
  (l1_nonneg pbar pbar).trans (rad_ge hα hpbar hpbar)

lemma L_bdd (u : Ω → A → ℝ) (α : A → ℝ) :
    BddAbove {x | ∃ a ∈ supp α, ∃ a' : A, a' ≠ a ∧ ∃ ω : Ω, x = |u ω a - u ω a'|} := by
  refine ((Set.finite_range (fun t : A × A × Ω => |u t.2.2 t.1 - u t.2.2 t.2.1|)).subset ?_).bddAbove
  rintro x ⟨a, _, a', _, ω, rfl⟩
  exact ⟨(a, a', ω), rfl⟩

lemma L_ge (u : Ω → A → ℝ) (α : A → ℝ) {a a' : A} (ha : a ∈ supp α) (ha' : a' ≠ a) (ω : Ω) :
    |u ω a - u ω a'| ≤ utilityRange u α :=
  le_csSup (L_bdd u α) ⟨a, ha, a', ha', ω, rfl⟩

lemma L_nonneg (u : Ω → A → ℝ) (α : A → ℝ) : 0 ≤ utilityRange u α :=
  Real.sSup_nonneg (by rintro x ⟨a, _, a', _, ω, rfl⟩; exact abs_nonneg _)

lemma M_bdd (v : Ω → A → ℝ) (α : A → ℝ) :
    BddAbove {x | ∃ a ∈ supp α, ∃ ω : Ω, x = |v ω a|} := by
  refine ((Set.finite_range (fun t : A × Ω => |v t.2 t.1|)).subset ?_).bddAbove
  rintro x ⟨a, _, ω, rfl⟩
  exact ⟨(a, ω), rfl⟩

lemma M_ge (v : Ω → A → ℝ) (α : A → ℝ) {a : A} (ha : a ∈ supp α) (ω : Ω) :
    |v ω a| ≤ senderBound v α :=
  le_csSup (M_bdd v α) ⟨a, ha, ω, rfl⟩

lemma M_nonneg (v : Ω → A → ℝ) (α : A → ℝ) : 0 ≤ senderBound v α :=
  Real.sSup_nonneg (by rintro x ⟨a, _, ω, rfl⟩; exact abs_nonneg _)

lemma pi_le_one {α : A → ℝ} {π : Ω → A → ℝ} (hπ : π ∈ supportedPolicies α) (ω : Ω) (a : A) :
    π ω a ≤ 1 := le_one_of_sum (π ω) (hπ.1 ω) (hπ.2.1 ω) a

lemma margin_lip (u : Ω → A → ℝ) (α : A → ℝ) {π : Ω → A → ℝ} (hπ : π ∈ supportedPolicies α)
    {a a' : A} (ha : a ∈ supp α) (ha' : a' ≠ a) (p q : Ω → ℝ) :
    |obedienceMargin u π a a' p - obedienceMargin u π a a' q| ≤
      utilityRange u α * l1Dist p q := by
  unfold obedienceMargin l1Dist
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ => ?_)
  have e : π ω a * p ω * (u ω a - u ω a') - π ω a * q ω * (u ω a - u ω a') =
      π ω a * (p ω - q ω) * (u ω a - u ω a') := by ring
  rw [e, abs_mul, abs_mul, abs_of_nonneg (hπ.1 ω a)]
  have h1 := pi_le_one hπ ω a
  have h2 := L_ge u α ha ha' ω
  have h3 := hπ.1 ω a
  calc π ω a * |p ω - q ω| * |u ω a - u ω a'|
      ≤ 1 * |p ω - q ω| * utilityRange u α := by gcongr
    _ = _ := by ring

lemma margin_ge (u : Ω → A → ℝ) {α : A → ℝ} (hα : α ∈ stdSimplex ℝ A) {π : Ω → A → ℝ}
    (hπ : π ∈ supportedPolicies α) {a a' : A} (ha : a ∈ supp α) (ha' : a' ≠ a)
    {pbar p : Ω → ℝ} (hpbar : pbar ∈ identifiedSet u α) (hp : p ∈ identifiedSet u α) :
    obedienceMargin u π a a' pbar - utilityRange u α * uncertaintyRadius u α pbar ≤
      obedienceMargin u π a a' p := by
  have h := (abs_le.mp (margin_lip u α hπ ha ha' p pbar)).1
  have h2 := mul_le_mul_of_nonneg_left (rad_ge hα hpbar hp) (L_nonneg u α)
  linarith

lemma margin_eq (u : Ω → A → ℝ) (π : Ω → A → ℝ) (a a' : A) (p : Ω → ℝ) :
    obedienceMargin u π a a' p = receiverObj u π p a a - receiverObj u π p a a' := by
  unfold obedienceMargin receiverObj
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

lemma om_mix (u : Ω → A → ℝ) (π π' : Ω → A → ℝ) (δ : ℝ) (a a' : A) (p : Ω → ℝ) :
    obedienceMargin u (fun ω a => (1 - δ) * π ω a + δ * π' ω a) a a' p =
      (1 - δ) * obedienceMargin u π a a' p + δ * obedienceMargin u π' a a' p := by
  unfold obedienceMargin
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

lemma sp_mix (v : Ω → A → ℝ) (α : A → ℝ) (μ : Ω → ℝ) (π π' : Ω → A → ℝ) (δ : ℝ) :
    senderPayoff v α (fun ω a => (1 - δ) * π ω a + δ * π' ω a) μ =
      (1 - δ) * senderPayoff v α π μ + δ * senderPayoff v α π' μ := by
  unfold senderPayoff
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

lemma mem_RO {u : Ω → A → ℝ} {α : A → ℝ} {π : Ω → A → ℝ} (hπ : π ∈ supportedPolicies α)
    (h : ∀ p ∈ identifiedSet u α, ∀ a ∈ supp α, ∀ a' : A, a' ≠ a →
      0 ≤ obedienceMargin u π a a' p) : π ∈ robustlyObedientPolicies u α := by
  refine ⟨hπ, fun μ hμ a ha a' => ?_⟩
  by_cases h' : a' = a
  · subst h'; simp
  · exact h μ hμ a ha a' h'

lemma term_zero {u v : Ω → A → ℝ} {α : A → ℝ} {π : Ω → A → ℝ} (hπ : π ∈ supportedPolicies α)
    (μ : Ω → ℝ) {s : A} (hs : s ∉ supp α) :
    sSup ((fun a => senderObj v π μ s a) '' bestResponses u π μ s) = 0 := by
  apply le_antisymm
  · exact Real.sSup_le (by rintro _ ⟨a, _, rfl⟩; simp [senderObj, hπ.2.2 _ s hs]) le_rfl
  · exact Real.sSup_nonneg (by rintro _ ⟨a, _, rfl⟩; simp [senderObj, hπ.2.2 _ s hs])

lemma unr_eq_supp {u v : Ω → A → ℝ} {α : A → ℝ} {π : Ω → A → ℝ} (hπ : π ∈ supportedPolicies α)
    (μ : Ω → ℝ) : unrestrictedPayoff u v π μ =
      ∑ s ∈ supp α, sSup ((fun a => senderObj v π μ s a) '' bestResponses u π μ s) := by
  unfold unrestrictedPayoff
  exact (Finset.sum_subset (Finset.subset_univ _) (fun s _ hs => term_zero hπ μ hs)).symm

lemma sp_eq (v : Ω → A → ℝ) (α : A → ℝ) (π : Ω → A → ℝ) (μ : Ω → ℝ) :
    senderPayoff v α π μ = ∑ s ∈ supp α, senderObj v π μ s s := by
  unfold senderPayoff senderObj
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ω _ => by ring

lemma mem_BR_of {u : Ω → A → ℝ} {π : Ω → A → ℝ} {μ : Ω → ℝ} {s : A}
    (h : ∀ a', 0 ≤ obedienceMargin u π s a' μ) : s ∈ bestResponses u π μ s := by
  intro a'
  have := h a'
  rw [margin_eq] at this
  linarith

lemma sp_le_unr {u v : Ω → A → ℝ} {α : A → ℝ} {π : Ω → A → ℝ}
    (hπ : π ∈ robustlyObedientPolicies u α) {μ : Ω → ℝ} (hμ : μ ∈ identifiedSet u α) :
    senderPayoff v α π μ ≤ unrestrictedPayoff u v π μ := by
  rw [unr_eq_supp hπ.1, sp_eq]
  refine Finset.sum_le_sum fun s hs => ?_
  apply le_csSup
  · exact ((Set.toFinite _).image _).bddAbove
  · exact ⟨s, mem_BR_of (fun a' => hπ.2 μ hμ s hs a'), rfl⟩

def bigC (v : Ω → A → ℝ) : ℝ := ∑ ω, ∑ a, |v ω a|

lemma bigC_nonneg (v : Ω → A → ℝ) : 0 ≤ bigC v :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma v_le_C (v : Ω → A → ℝ) (ω : Ω) (a : A) : |v ω a| ≤ bigC v := by
  unfold bigC
  calc |v ω a| ≤ ∑ a', |v ω a'| :=
        Finset.single_le_sum (f := fun a' => |v ω a'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    _ ≤ ∑ ω', ∑ a', |v ω' a'| :=
        Finset.single_le_sum (f := fun ω' => ∑ a', |v ω' a'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ ω)

lemma unr_le_C {S : Type*} [Fintype S] (u v : Ω → A → ℝ) (π : Ω → S → ℝ)
    (hπ : IsSignalingPolicy π) {μ : Ω → ℝ} (hμ : (∀ ω, 0 ≤ μ ω) ∧ ∑ ω, μ ω = 1) :
    unrestrictedPayoff u v π μ ≤ bigC v := by
  unfold unrestrictedPayoff
  have hC := bigC_nonneg v
  calc ∑ s, sSup ((fun a => senderObj v π μ s a) '' bestResponses u π μ s)
      ≤ ∑ s, bigC v * ∑ ω, π ω s * μ ω := by
        refine Finset.sum_le_sum fun s _ => Real.sSup_le ?_
          (mul_nonneg hC (Finset.sum_nonneg fun ω _ => mul_nonneg (hπ.1 ω s) (hμ.1 ω)))
        rintro _ ⟨a, _, rfl⟩
        unfold senderObj
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun ω _ => ?_
        have := v_le_C v ω a
        have h0 : 0 ≤ π ω s * μ ω := mul_nonneg (hπ.1 ω s) (hμ.1 ω)
        calc π ω s * μ ω * v ω a ≤ π ω s * μ ω * |v ω a| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) h0
          _ ≤ π ω s * μ ω * bigC v := mul_le_mul_of_nonneg_left this h0
          _ = bigC v * (π ω s * μ ω) := by ring
    _ = bigC v := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        have : ∀ ω, ∑ s, π ω s * μ ω = μ ω := fun ω => by
          rw [← Finset.sum_mul, hπ.2 ω, one_mul]
        simp_rw [this]
        rw [hμ.2, mul_one]

lemma sInf_le_of {S : Set ℝ} {c x : ℝ} (hx : x ∈ S) (hxc : x ≤ c) (hc : 0 ≤ c) : sInf S ≤ c := by
  by_cases hb : BddBelow S
  · exact (csInf_le hb hx).trans hxc
  · rw [Real.sInf_of_not_bddBelow hb]; exact hc

lemma sp_abs_le {v : Ω → A → ℝ} {α : A → ℝ} {π : Ω → A → ℝ} {μ : Ω → ℝ}
    (hπ : π ∈ supportedPolicies α) (hμ : (∀ ω, 0 ≤ μ ω) ∧ ∑ ω, μ ω = 1) :
    |senderPayoff v α π μ| ≤ senderBound v α := by
  unfold senderPayoff
  have hrow : ∀ ω, ∑ a ∈ supp α, π ω a = 1 := fun ω => by
    have := Finset.sum_subset (s₁ := supp α) (s₂ := Finset.univ) (f := fun a => π ω a)
      (Finset.subset_univ _) (fun a _ ha => hπ.2.2 ω a ha)
    rw [this, hπ.2.1 ω]
  calc |∑ ω, ∑ a ∈ supp α, μ ω * π ω a * v ω a|
      ≤ ∑ ω, |∑ a ∈ supp α, μ ω * π ω a * v ω a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, μ ω * senderBound v α := by
        refine Finset.sum_le_sum fun ω _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ a ∈ supp α, |μ ω * π ω a * v ω a|
            ≤ ∑ a ∈ supp α, μ ω * π ω a * senderBound v α :=
              Finset.sum_le_sum fun a ha => by
                rw [abs_mul, abs_of_nonneg (mul_nonneg (hμ.1 ω) (hπ.1 ω a))]
                exact mul_le_mul_of_nonneg_left (M_ge v α ha ω)
                  (mul_nonneg (hμ.1 ω) (hπ.1 ω a))
          _ = μ ω * senderBound v α := by
              rw [← Finset.sum_mul, ← Finset.mul_sum, hrow, mul_one]
    _ = senderBound v α := by rw [← Finset.sum_mul, hμ.2, one_mul]

lemma V_bddBelow {u v : Ω → A → ℝ} {α : A → ℝ} (hα : α ∈ stdSimplex ℝ A)
    {π : Ω → A → ℝ} (hπ : π ∈ supportedPolicies α) :
    BddBelow ((fun μ => senderPayoff v α π μ) '' identifiedSet u α) :=
  ⟨-senderBound v α, by
    rintro _ ⟨q, hq, rfl⟩
    linarith [(abs_le.mp (sp_abs_le (v := v) hπ (ident_mem hα hq))).1]⟩

lemma Y_bdd {u v : Ω → A → ℝ} {α : A → ℝ} (hα : α ∈ stdSimplex ℝ A) {pbar : Ω → ℝ}
    (hpbar : pbar ∈ identifiedSet u α) :
    BddAbove {x | ∃ π ∈ robustlyObedientPolicies u α,
      x = sInf ((fun μ => senderPayoff v α π μ) '' identifiedSet u α)} :=
  ⟨senderBound v α, by
    rintro _ ⟨π, hπ, rfl⟩
    exact sInf_le_of ⟨pbar, hpbar, rfl⟩
      (abs_le.mp (sp_abs_le (v := v) hπ.1 (ident_mem hα hpbar))).2 (M_nonneg v α)⟩

lemma unr_relabel (u v : Ω → A → ℝ) {m : ℕ} (e : A ≃ Fin m) (π : Ω → A → ℝ) (μ : Ω → ℝ) :
    unrestrictedPayoff u v (fun ω i => π ω (e.symm i)) μ = unrestrictedPayoff u v π μ := by
  unfold unrestrictedPayoff
  exact Equiv.sum_comp e.symm
    (fun s => sSup ((fun a => senderObj v π μ s a) '' bestResponses u π μ s))

lemma robust_le_unr {u v : Ω → A → ℝ} {α : A → ℝ} (hα : α ∈ stdSimplex ℝ A) {pbar : Ω → ℝ}
    (hpbar : pbar ∈ identifiedSet u α) {π0 : Ω → A → ℝ}
    (h0 : π0 ∈ robustlyObedientPolicies u α) : robustValue u v α ≤ unrestrictedValue u v α := by
  apply csSup_le
  · exact ⟨sInf ((fun μ => senderPayoff v α π0 μ) '' identifiedSet u α), π0, h0, rfl⟩
  rintro x ⟨π, hπ, rfl⟩
  obtain ⟨m, ⟨e⟩⟩ : ∃ m, Nonempty (A ≃ Fin m) := ⟨_, ⟨Fintype.equivFin A⟩⟩
  have hsig : IsSignalingPolicy (fun ω i => π ω (e.symm i)) :=
    ⟨fun ω i => hπ.1.1 ω _, fun ω => by
      rw [Equiv.sum_comp e.symm (fun a => π ω a)]; exact hπ.1.2.1 ω⟩
  have h1 : sInf ((fun μ => senderPayoff v α π μ) '' identifiedSet u α) ≤
      sInf ((fun μ => unrestrictedPayoff u v (fun ω i => π ω (e.symm i)) μ) ''
        identifiedSet u α) := by
    apply le_csInf (Set.Nonempty.image _ ⟨pbar, hpbar⟩)
    rintro _ ⟨μ, hμ, rfl⟩
    show _ ≤ unrestrictedPayoff u v (fun ω i => π ω (e.symm i)) μ
    rw [unr_relabel]
    exact (csInf_le (V_bddBelow hα hπ.1) ⟨μ, hμ, rfl⟩).trans (sp_le_unr hπ hμ)
  refine h1.trans (le_csSup ?_ ⟨m, _, hsig, rfl⟩)
  exact ⟨bigC v, by
    rintro _ ⟨m', π', hπ', rfl⟩
    exact sInf_le_of ⟨pbar, hpbar, rfl⟩ (unr_le_C u v π' hπ' (ident_mem hα hpbar))
      (bigC_nonneg v)⟩

end

end RobustObedientPersuasion.Saddle.Supplement.Dev
end

section
namespace RobustObedientPersuasion.Saddle.Supplement
open RobustObedientPersuasion.Saddle.Supplement.Dev

theorem chk_theorem_4_4 {Ω A : Type*} [Fintype Ω] [Fintype A]
    (u v : Ω → A → ℝ) (α : A → ℝ) (hα : α ∈ stdSimplex ℝ A)
    (hdom : NoSupportedActionDominated u α)
    (pbar : Ω → ℝ) (hpbar : pbar ∈ identifiedSet u α)
    (πstar : Ω → A → ℝ) (hopt : IsUnrestrictedMaxminOptimalDirect u v α πstar)
    (hobed : ∀ a ∈ supp α, ∀ a' : A, a' ≠ a → 0 ≤ obedienceMargin u πstar a a' pbar)
    (πint : Ω → A → ℝ) (hint : πint ∈ supportedPolicies α) (η : ℝ) (hη : 0 < η)
    (hintη : ∀ a ∈ supp α, ∀ a' : A, a' ≠ a → ∀ p ∈ identifiedSet u α,
      η ≤ obedienceMargin u πint a a' p) :
    let δ := utilityRange u α * uncertaintyRadius u α pbar /
      (η + utilityRange u α * uncertaintyRadius u α pbar)
    let πδ : Ω → A → ℝ := fun ω a => (1 - δ) * πstar ω a + δ * πint ω a
    -- (i) Policy Robustification
    πδ ∈ robustlyObedientPolicies u α ∧
    -- (ii) Payoff Bound under Receiver Action Stability
    (ReceiverActionStable u v α πstar πδ →
      0 ≤ unrestrictedValue u v α - robustValue u v α ∧
      unrestrictedValue u v α - robustValue u v α ≤
        (2 * senderBound v α * utilityRange u α / η) * uncertaintyRadius u α pbar) := by
  intro δ πδ
  have hπ := hopt.1
  have hL := L_nonneg u α
  have hr := rad_nonneg hα hpbar
  have hLr : 0 ≤ utilityRange u α * uncertaintyRadius u α pbar := mul_nonneg hL hr
  have hden : 0 < η + utilityRange u α * uncertaintyRadius u α pbar := by linarith
  have hδdef : δ = utilityRange u α * uncertaintyRadius u α pbar /
      (η + utilityRange u α * uncertaintyRadius u α pbar) := rfl
  have hδ0 : 0 ≤ δ := by rw [hδdef]; exact div_nonneg hLr hden.le
  have hδ : δ * (η + utilityRange u α * uncertaintyRadius u α pbar) =
      utilityRange u α * uncertaintyRadius u α pbar := by
    rw [hδdef]; exact div_mul_cancel₀ _ hden.ne'
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hden]; linarith
  have hδη : δ ≤ utilityRange u α * uncertaintyRadius u α pbar / η := by
    rw [hδdef]
    exact div_le_div_of_nonneg_left hLr hη (by linarith)
  have hsupδ : πδ ∈ supportedPolicies α :=
    ⟨fun ω a => add_nonneg (mul_nonneg (by linarith) (hπ.1 ω a)) (mul_nonneg hδ0 (hint.1 ω a)),
     fun ω => by
      show ∑ a, ((1 - δ) * πstar ω a + δ * πint ω a) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hπ.2.1 ω, hint.2.1 ω]
      ring,
     fun ω a ha => by
      show (1 - δ) * πstar ω a + δ * πint ω a = 0
      rw [hπ.2.2 ω a ha, hint.2.2 ω a ha]; ring⟩
  have hROδ : πδ ∈ robustlyObedientPolicies u α := by
    refine mem_RO hsupδ fun p hp a ha a' ha' => ?_
    have h1 := margin_ge u hα hπ ha ha' hpbar hp
    have h2 := hobed a ha a' ha'
    have h3 := hintη a ha a' ha' p hp
    rw [show obedienceMargin u πδ a a' p = _ from om_mix u πstar πint δ a a' p]
    have h4 : 0 ≤ (1 - δ) * (obedienceMargin u πstar a a' p +
        utilityRange u α * uncertaintyRadius u α pbar) :=
      mul_nonneg (by linarith) (by linarith)
    have h5 : 0 ≤ δ * (obedienceMargin u πint a a' p - η) := mul_nonneg hδ0 (by linarith)
    nlinarith
  refine ⟨hROδ, fun hstab => ?_⟩
  have hunr : ∀ p ∈ identifiedSet u α,
      unrestrictedPayoff u v πstar p = senderPayoff v α πstar p := by
    intro p hp
    rw [unr_eq_supp hπ, sp_eq]
    exact Finset.sum_congr rfl fun s hs => (hstab s hs p hp).2.2.symm
  have hW : unrestrictedValue u v α =
      sInf ((fun μ => senderPayoff v α πstar μ) '' identifiedSet u α) := by
    rw [← hopt.2]
    exact congrArg sInf (Set.image_congr hunr)
  have hle := robust_le_unr (v := v) hα hpbar hROδ
  have hRδ : sInf ((fun μ => senderPayoff v α πδ μ) '' identifiedSet u α) ≤ robustValue u v α :=
    le_csSup (Y_bdd hα hpbar) ⟨πδ, hROδ, rfl⟩
  have hM := M_nonneg v α
  have hkey : unrestrictedValue u v α - 2 * senderBound v α * δ ≤
      sInf ((fun μ => senderPayoff v α πδ μ) '' identifiedSet u α) := by
    apply le_csInf (Set.Nonempty.image _ ⟨pbar, hpbar⟩)
    rintro _ ⟨p, hp, rfl⟩
    have h1 : sInf ((fun μ => senderPayoff v α πstar μ) '' identifiedSet u α) ≤
        senderPayoff v α πstar p := csInf_le (V_bddBelow hα hπ) ⟨p, hp, rfl⟩
    have hmix : senderPayoff v α πδ p = (1 - δ) * senderPayoff v α πstar p +
        δ * senderPayoff v α πint p := sp_mix v α p πstar πint δ
    have hb1 := abs_le.mp (sp_abs_le (v := v) hπ (ident_mem hα hp))
    have hb2 := abs_le.mp (sp_abs_le (v := v) hint (ident_mem hα hp))
    have h2 : δ * (senderPayoff v α πstar p - senderPayoff v α πint p) ≤
        δ * (2 * senderBound v α) :=
      mul_le_mul_of_nonneg_left (by linarith [hb1.2, hb2.1]) hδ0
    show _ ≤ senderPayoff v α πδ p
    rw [hW]
    nlinarith
  refine ⟨by linarith, ?_⟩
  have h6 : 2 * senderBound v α * δ ≤ 2 * senderBound v α *
      (utilityRange u α * uncertaintyRadius u α pbar / η) :=
    mul_le_mul_of_nonneg_left hδη (by linarith)
  have h7 : 2 * senderBound v α * (utilityRange u α * uncertaintyRadius u α pbar / η) =
      2 * senderBound v α * utilityRange u α / η * uncertaintyRadius u α pbar := by ring
  linarith

end RobustObedientPersuasion.Saddle.Supplement
end

theorem solution : type_of% @RobustObedientPersuasion.Saddle.Supplement.chk_theorem_4_4 := @RobustObedientPersuasion.Saddle.Supplement.chk_theorem_4_4
