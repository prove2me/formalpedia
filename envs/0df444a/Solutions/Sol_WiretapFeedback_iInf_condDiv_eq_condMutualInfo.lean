-- Prove2me | solution 1 for WiretapFeedback.iInf_condDiv_eq_condMutualInfo
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T05:57:19.477041+00:00
-- url     : https://prove2.me/submissions/1f08d346-cd4f-4525-9589-59e24b6f9578

import Mathlib
import Definitions.Def_WildeQIT_condMutualInfo
import Definitions.Def_WiretapFeedback_condDiv
import Definitions.Def_WiretapFeedback_degradedChannel
import Definitions.Def_WiretapFeedback_eveMarginal

namespace CondDivAux

open WiretapFeedback WildeQIT

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- The optimal approximant `Q*(x,y,z) = P_XZ(x,z) P_YZ(y,z) / P_Z(z)`. -/
noncomputable def Qs (P : FinDist (X × Y × Z)) (t : X × Y × Z) : ℝ :=
  P.margXZ.prob (t.1, t.2.2) * P.margYZ.prob t.2 / P.margYZ.snd.prob t.2.2

lemma le_margXZ (P : FinDist (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    P.prob (x, y, z) ≤ P.margXZ.prob (x, z) := by
  show P.prob (x, y, z) ≤ ∑ y', P.prob (x, y', z)
  exact Finset.single_le_sum (f := fun y' => P.prob (x, y', z)) (fun y' _ => P.nonneg _)
    (Finset.mem_univ y)

lemma le_margYZ (P : FinDist (X × Y × Z)) (x : X) (y : Y) (z : Z) :
    P.prob (x, y, z) ≤ P.margYZ.prob (y, z) := by
  show P.prob (x, y, z) ≤ ∑ x', P.prob (x', y, z)
  exact Finset.single_le_sum (f := fun x' => P.prob (x', y, z)) (fun x' _ => P.nonneg _)
    (Finset.mem_univ x)

lemma margYZ_le (P : FinDist (X × Y × Z)) (y : Y) (z : Z) :
    P.margYZ.prob (y, z) ≤ P.margYZ.snd.prob z := by
  show P.margYZ.prob (y, z) ≤ ∑ y', P.margYZ.prob (y', z)
  exact Finset.single_le_sum (f := fun y' => P.margYZ.prob (y', z)) (fun y' _ => P.margYZ.nonneg _)
    (Finset.mem_univ y)

lemma margXZ_le (P : FinDist (X × Y × Z)) (x : X) (z : Z) :
    P.margXZ.prob (x, z) ≤ P.margYZ.snd.prob z := by
  show ∑ y, P.prob (x, y, z) ≤ ∑ y, ∑ x', P.prob (x', y, z)
  exact Finset.sum_le_sum fun y _ => Finset.single_le_sum (f := fun x' => P.prob (x', y, z))
    (fun x' _ => P.nonneg _) (Finset.mem_univ x)

lemma support_sub_Qs (P : FinDist (X × Y × Z)) :
    Function.support P.prob ⊆ Function.support (Qs P) := by
  intro t ht
  obtain ⟨x, y, z⟩ := t
  have hpos : 0 < P.prob (x, y, z) := lt_of_le_of_ne (P.nonneg _) (Ne.symm ht)
  have h1 := lt_of_lt_of_le hpos (le_margXZ P x y z)
  have h2 := lt_of_lt_of_le hpos (le_margYZ P x y z)
  have h3 := lt_of_lt_of_le h2 (margYZ_le P y z)
  simp only [Function.mem_support, Qs]
  positivity

/-- Termwise decomposition `log(P/Q*) = log(P/P_XZ) − log(P_YZ/P_Z)` on the support. -/
lemma term_eq (P : FinDist (X × Y × Z)) (t : X × Y × Z) :
    P.prob t * Real.logb 2 (P.prob t / Qs P t) =
      P.prob t * Real.logb 2 (P.prob t / P.margXZ.prob (t.1, t.2.2)) -
        P.prob t * Real.logb 2 (P.margYZ.prob t.2 / P.margYZ.snd.prob t.2.2) := by
  obtain ⟨x, y, z⟩ := t
  by_cases h0 : P.prob (x, y, z) = 0
  · simp [h0]
  have hpos : 0 < P.prob (x, y, z) := lt_of_le_of_ne (P.nonneg _) (Ne.symm h0)
  have h1 := lt_of_lt_of_le hpos (le_margXZ P x y z)
  have h2 := lt_of_lt_of_le hpos (le_margYZ P x y z)
  have h3 := lt_of_lt_of_le h2 (margYZ_le P y z)
  rw [← mul_sub]
  congr 1
  simp only [Qs]
  rw [Real.logb_div hpos.ne' (by positivity), Real.logb_div hpos.ne' h1.ne',
    Real.logb_div h2.ne' h3.ne', Real.logb_div (by positivity) h3.ne',
    Real.logb_mul h1.ne' h2.ne']
  ring

/-- `D(P ‖ Q*) = I(X;Y|Z)` (real form). -/
lemma sum_eq_condMutualInfo (P : FinDist (X × Y × Z)) :
    ∑ t, P.prob t * Real.logb 2 (P.prob t / Qs P t) = condMutualInfo P := by
  simp only [term_eq, Finset.sum_sub_distrib]
  unfold condMutualInfo condEntropy
  have hA : ∑ t : X × Y × Z, P.prob t * Real.logb 2 (P.prob t / P.margXZ.prob (t.1, t.2.2)) =
      ∑ y : Y, ∑ xz : X × Z, P.groupY_XZ.prob (y, xz) *
        Real.logb 2 (P.groupY_XZ.prob (y, xz) / P.groupY_XZ.snd.prob xz) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, FinDist.groupY_XZ_prob]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun z _ => ?_
    rfl
  have hB : ∑ t : X × Y × Z, P.prob t * Real.logb 2 (P.margYZ.prob t.2 / P.margYZ.snd.prob t.2.2) =
      ∑ y : Y, ∑ z : Z, P.margYZ.prob (y, z) *
        Real.logb 2 (P.margYZ.prob (y, z) / P.margYZ.snd.prob z) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    rw [← Finset.sum_mul]
    rfl
  rw [hA, hB]
  ring

lemma relEntropy_Qs (P : FinDist (X × Y × Z)) :
    relEntropy P (Qs P) = ((condMutualInfo P : ℝ) : EReal) := by
  unfold relEntropy
  rw [if_pos (support_sub_Qs P), sum_eq_condMutualInfo]

lemma QV_apply (p : FinDist X) (W : Channel X (Y × Z)) (V₁ : Channel Z Y) (x : X) (y : Y) (z : Z) :
    (jointLaw p (degradedChannel (eveMarginal W) V₁)).prob (x, y, z) =
      (jointLaw p W).margXZ.prob (x, z) * (V₁ z).prob y := by
  show p.prob x * ((W x).snd.prob z * (V₁ z).prob y) = (∑ y', p.prob x * (W x).prob (y', z)) * _
  rw [← Finset.mul_sum, FinDist.snd_prob]
  ring

/-- Gibbs step: `Σ P log(P/Q*) ≤ Σ P log(P/Q_V)` when `supp P ⊆ supp Q_V`. -/
lemma gibbs (P : FinDist (X × Y × Z)) (V₁ : Channel Z Y)
    (hsupp : ∀ t : X × Y × Z, P.prob t ≠ 0 → P.margXZ.prob (t.1, t.2.2) * (V₁ t.2.2).prob t.2.1 ≠ 0) :
    ∑ t, P.prob t * Real.logb 2 (P.prob t / Qs P t) ≤
      ∑ t, P.prob t * Real.logb 2 (P.prob t / (P.margXZ.prob (t.1, t.2.2) * (V₁ t.2.2).prob t.2.1)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set e : X × Y × Z → ℝ := fun t => (P.prob t - P.prob t * (P.margYZ.snd.prob t.2.2 *
    (V₁ t.2.2).prob t.2.1 / P.margYZ.prob t.2)) / Real.log 2 with he
  have hterm : ∀ t, e t ≤ P.prob t * Real.logb 2 (P.prob t /
      (P.margXZ.prob (t.1, t.2.2) * (V₁ t.2.2).prob t.2.1)) -
      P.prob t * Real.logb 2 (P.prob t / Qs P t) := by
    intro t
    obtain ⟨x, y, z⟩ := t
    by_cases h0 : P.prob (x, y, z) = 0
    · simp [he, h0]
    have hpos : 0 < P.prob (x, y, z) := lt_of_le_of_ne (P.nonneg _) (Ne.symm h0)
    have h1 := lt_of_lt_of_le hpos (le_margXZ P x y z)
    have h2 := lt_of_lt_of_le hpos (le_margYZ P x y z)
    have h3 := lt_of_lt_of_le h2 (margYZ_le P y z)
    have hV : 0 < (V₁ z).prob y := by
      have := hsupp (x, y, z) h0
      have hnn := (V₁ z).nonneg y
      rcases lt_or_eq_of_le hnn with h | h
      · exact h
      · exfalso; apply this; simp [← h]
    simp only [he, Qs]
    rw [← mul_sub, Real.logb_div hpos.ne' (by positivity), Real.logb_div hpos.ne' (by positivity)]
    have key : Real.logb 2 (P.margXZ.prob (x, z) * P.margYZ.prob (y, z) / P.margYZ.snd.prob z) -
        Real.logb 2 (P.margXZ.prob (x, z) * (V₁ z).prob y) =
        Real.logb 2 (P.margYZ.prob (y, z) / (P.margYZ.snd.prob z * (V₁ z).prob y)) := by
      rw [Real.logb_div (by positivity) (by positivity), Real.logb_mul h1.ne' h2.ne',
        Real.logb_mul h1.ne' hV.ne', Real.logb_div h2.ne' (by positivity),
        Real.logb_mul h3.ne' hV.ne']
      ring
    have hlb : (1 - (P.margYZ.snd.prob z * (V₁ z).prob y / P.margYZ.prob (y, z))) / Real.log 2 ≤
        Real.logb 2 (P.margYZ.prob (y, z) / (P.margYZ.snd.prob z * (V₁ z).prob y)) := by
      unfold Real.logb
      rw [div_le_div_iff_of_pos_right hlog2]
      have := Real.one_sub_inv_le_log_of_pos
        (show 0 < P.margYZ.prob (y, z) / (P.margYZ.snd.prob z * (V₁ z).prob y) by positivity)
      rwa [inv_div] at this
    calc (P.prob (x, y, z) - P.prob (x, y, z) * (P.margYZ.snd.prob z * (V₁ z).prob y /
          P.margYZ.prob (y, z))) / Real.log 2
        = P.prob (x, y, z) * ((1 - (P.margYZ.snd.prob z * (V₁ z).prob y /
          P.margYZ.prob (y, z))) / Real.log 2) := by ring
      _ ≤ P.prob (x, y, z) * Real.logb 2 (P.margYZ.prob (y, z) /
          (P.margYZ.snd.prob z * (V₁ z).prob y)) := by gcongr
      _ = _ := by rw [← key]; ring
  -- the error terms sum to something nonnegative
  have hsum_e : 0 ≤ ∑ t, e t := by
    simp only [he, ← Finset.sum_div]
    refine div_nonneg ?_ hlog2.le
    rw [Finset.sum_sub_distrib, P.sum_eq_one, sub_nonneg]
    have h1 : ∑ t : X × Y × Z, P.prob t * (P.margYZ.snd.prob t.2.2 * (V₁ t.2.2).prob t.2.1 /
        P.margYZ.prob t.2) = ∑ y : Y, ∑ z : Z, P.margYZ.prob (y, z) *
          (P.margYZ.snd.prob z * (V₁ z).prob y / P.margYZ.prob (y, z)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
      rw [← Finset.sum_mul]
      rfl
    rw [h1]
    calc ∑ y : Y, ∑ z : Z, P.margYZ.prob (y, z) *
          (P.margYZ.snd.prob z * (V₁ z).prob y / P.margYZ.prob (y, z))
        ≤ ∑ y : Y, ∑ z : Z, P.margYZ.snd.prob z * (V₁ z).prob y := by
          refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun z _ => ?_
          by_cases hyz : P.margYZ.prob (y, z) = 0
          · rw [hyz, zero_mul]; exact mul_nonneg (P.margYZ.snd.nonneg _) ((V₁ z).nonneg _)
          · rw [mul_div_cancel₀ _ hyz]
      _ = 1 := by
          rw [Finset.sum_comm]
          simp_rw [← Finset.mul_sum, (V₁ _).sum_eq_one, mul_one]
          exact P.margYZ.snd.sum_eq_one
  have := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hterm t
  rw [Finset.sum_sub_distrib] at this
  linarith

end CondDivAux

open CondDivAux WildeQIT in
theorem solution {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (W : WildeQIT.Channel X (Y × Z)) (p : WildeQIT.FinDist X) :
    let P := WiretapFeedback.jointLaw p W
    (⨅ V₁ : WildeQIT.Channel Z Y, WiretapFeedback.condDiv W
        (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) V₁) p) =
        WildeQIT.relEntropy P
          (fun t => P.margXZ.prob (t.1, t.2.2) * P.margYZ.prob t.2 / P.margYZ.snd.prob t.2.2) ∧
      WildeQIT.relEntropy P
          (fun t => P.margXZ.prob (t.1, t.2.2) * P.margYZ.prob t.2 / P.margYZ.snd.prob t.2.2) =
        ((WildeQIT.condMutualInfo P : ℝ) : EReal) := by
  intro P
  refine ⟨?_, relEntropy_Qs P⟩
  -- every degraded approximant is worse than `Q*`
  have hlow : ∀ V₁ : Channel Z Y, relEntropy P (Qs P) ≤ WiretapFeedback.condDiv W
      (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) V₁) p := by
    intro V₁
    unfold WiretapFeedback.condDiv
    have hQV : (WiretapFeedback.jointLaw p (WiretapFeedback.degradedChannel
        (WiretapFeedback.eveMarginal W) V₁)).prob =
        fun t => P.margXZ.prob (t.1, t.2.2) * (V₁ t.2.2).prob t.2.1 := by
      funext t
      obtain ⟨x, y, z⟩ := t
      exact QV_apply p W V₁ x y z
    rw [hQV]
    unfold relEntropy
    rw [if_pos (support_sub_Qs P)]
    split_ifs with hs
    · refine EReal.coe_le_coe_iff.mpr (gibbs P V₁ fun t ht => ?_)
      exact hs ht
    · exact le_top
  -- the optimal channel `V₁* = P_{Y|Z}`
  obtain ⟨x0⟩ : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := p.sum_eq_one
    simp at this
  have hY : Nonempty Y := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := (W x0).sum_eq_one
    simp at this
  have hcard : (Fintype.card Y : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  let Vs : Channel Z Y := fun z =>
    { prob := fun y => if P.margYZ.snd.prob z = 0 then (Fintype.card Y : ℝ)⁻¹
        else P.margYZ.prob (y, z) / P.margYZ.snd.prob z
      nonneg := fun y => by
        split_ifs
        · positivity
        · exact div_nonneg (P.margYZ.nonneg _) (P.margYZ.snd.nonneg _)
      sum_eq_one := by
        split_ifs with hz
        · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard]
        · rw [← Finset.sum_div]
          exact div_self hz }
  have hopt : WiretapFeedback.condDiv W
      (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) Vs) p =
      relEntropy P (Qs P) := by
    unfold WiretapFeedback.condDiv
    congr 1
    funext t
    obtain ⟨x, y, z⟩ := t
    rw [QV_apply]
    show P.margXZ.prob (x, z) * (if P.margYZ.snd.prob z = 0 then (Fintype.card Y : ℝ)⁻¹
        else P.margYZ.prob (y, z) / P.margYZ.snd.prob z) = Qs P (x, y, z)
    unfold Qs
    split_ifs with hz
    · have : P.margXZ.prob (x, z) = 0 :=
        le_antisymm (hz ▸ margXZ_le P x z) (P.margXZ.nonneg _)
      simp [this, hz]
    · rw [mul_div_assoc]
  exact le_antisymm (iInf_le_of_le Vs (le_of_eq hopt)) (le_iInf hlow)
