-- Prove2me | solution 1 for WiretapFeedback.minimax_condDiv_eq_max_condMutualInfo
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T06:12:48.311495+00:00
-- url     : https://prove2.me/submissions/896bf97e-eb06-47cd-a2c6-bf37178af528

import Mathlib
import Definitions.Def_WildeQIT_condMutualInfo
import Definitions.Def_WiretapFeedback_condDiv
import Definitions.Def_WiretapFeedback_degradedChannel
import Definitions.Def_WiretapFeedback_eveMarginal
import Theorems.Thm_WiretapFeedback_iInf_condDiv_eq_condMutualInfo

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

namespace CondDivAux

open WiretapFeedback WildeQIT

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- The divergence-minimising channel `V₁* = P_{Y|Z}` (uniform where `P_Z = 0`). -/
lemma exists_opt (W : Channel X (Y × Z)) (p : FinDist X) :
    ∃ Vs : Channel Z Y, condDiv W (degradedChannel (eveMarginal W) Vs) p =
      relEntropy (jointLaw p W) (Qs (jointLaw p W)) := by
  set P := jointLaw p W
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
  refine ⟨Vs, ?_⟩
  unfold condDiv
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
    simp [this]
  · rw [mul_div_assoc]

end CondDivAux

namespace MinimaxAux

open WiretapFeedback WildeQIT

variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]

/-- Eve's marginal `W_Z(z|x)`. -/
noncomputable def WZ (W : Channel X (Y × Z)) (x : X) (z : Z) : ℝ := (W x).snd.prob z

lemma W_le_WZ (W : Channel X (Y × Z)) (x : X) (y : Y) (z : Z) :
    (W x).prob (y, z) ≤ WZ W x z := by
  show (W x).prob (y, z) ≤ ∑ y', (W x).prob (y', z)
  exact Finset.single_le_sum (f := fun y' => (W x).prob (y', z)) (fun y' _ => (W x).nonneg _)
    (Finset.mem_univ y)

/-- The constant part `A_x = Σ W log(W/W_Z)`. -/
noncomputable def Acoef (W : Channel X (Y × Z)) (x : X) : ℝ :=
  ∑ y, ∑ z, (W x).prob (y, z) * Real.logb 2 ((W x).prob (y, z) / WZ W x z)

/-- The explicit objective on full-support channels:
`G(V,p) = Σ_x p(x) A_x − Σ_{x,y,z} p(x) W(y,z|x) log V(y|z)`. -/
noncomputable def G (W : Channel X (Y × Z)) (V : Z → Y → ℝ) (p : X → ℝ) : ℝ :=
  ∑ x, p x * Acoef W x - ∑ x, ∑ y, ∑ z, p x * (W x).prob (y, z) * Real.logb 2 (V z y)

lemma Q_apply (W : Channel X (Y × Z)) (V₁ : Channel Z Y) (pd : FinDist X) (x : X) (y : Y) (z : Z) :
    (jointLaw pd (degradedChannel (eveMarginal W) V₁)).prob (x, y, z) =
      pd.prob x * (WZ W x z * (V₁ z).prob y) := rfl

lemma deg_apply (W : Channel X (Y × Z)) (V₁ : Channel Z Y) (x : X) (y : Y) (z : Z) :
    (degradedChannel (eveMarginal W) V₁ x).prob (y, z) = WZ W x z * (V₁ z).prob y := rfl

lemma P_apply (W : Channel X (Y × Z)) (pd : FinDist X) (x : X) (y : Y) (z : Z) :
    (jointLaw pd W).prob (x, y, z) = pd.prob x * (W x).prob (y, z) := rfl

/-- The relative-entropy term of `condDiv` against a degraded channel. -/
lemma term_rewrite (W : Channel X (Y × Z)) (V₁ : Channel Z Y) (pd : FinDist X) (x : X) (y : Y)
    (z : Z) (hV : 0 < (V₁ z).prob y ∨ pd.prob x * (W x).prob (y, z) = 0) :
    pd.prob x * (W x).prob (y, z) * Real.logb 2 (pd.prob x * (W x).prob (y, z) /
      (pd.prob x * (WZ W x z * (V₁ z).prob y))) =
    pd.prob x * ((W x).prob (y, z) * Real.logb 2 ((W x).prob (y, z) / WZ W x z)) -
      pd.prob x * (W x).prob (y, z) * Real.logb 2 ((V₁ z).prob y) := by
  by_cases h0 : pd.prob x * (W x).prob (y, z) = 0
  · rcases mul_eq_zero.mp h0 with h | h <;> simp [h]
  have hp : 0 < pd.prob x := lt_of_le_of_ne (pd.nonneg x) (fun h => h0 (by rw [← h, zero_mul]))
  have hw : 0 < (W x).prob (y, z) :=
    lt_of_le_of_ne ((W x).nonneg _) (fun h => h0 (by rw [← h, mul_zero]))
  have hz : 0 < WZ W x z := lt_of_lt_of_le hw (W_le_WZ W x y z)
  have hv : 0 < (V₁ z).prob y := hV.resolve_right h0
  rw [show pd.prob x * (W x).prob (y, z) / (pd.prob x * (WZ W x z * (V₁ z).prob y)) =
    (W x).prob (y, z) / WZ W x z / (V₁ z).prob y by field_simp,
    Real.logb_div (by positivity) hv.ne']
  ring

set_option linter.unusedSectionVars false

/-- On a support-compatible pair, the divergence is the explicit sum. -/
lemma D_sum (W : Channel X (Y × Z)) (V₁ : Channel Z Y) (pd : FinDist X)
    (hs : ∀ x y z, pd.prob x * (W x).prob (y, z) ≠ 0 → 0 < (V₁ z).prob y) :
    ∑ t, (jointLaw pd W).prob t * Real.logb 2 ((jointLaw pd W).prob t /
      (jointLaw pd (degradedChannel (eveMarginal W) V₁)).prob t) =
    G W (fun z y => (V₁ z).prob y) pd.prob := by
  unfold G Acoef
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, P_apply, Q_apply, deg_apply]
  have hterm : ∀ x y z, pd.prob x * (W x).prob (y, z) * Real.logb 2 (pd.prob x * (W x).prob (y, z) /
      (pd.prob x * (WZ W x z * (V₁ z).prob y))) =
      pd.prob x * ((W x).prob (y, z) * Real.logb 2 ((W x).prob (y, z) / WZ W x z)) -
        pd.prob x * (W x).prob (y, z) * Real.logb 2 ((V₁ z).prob y) := by
    intro x y z
    refine term_rewrite W V₁ pd x y z ?_
    by_cases h : pd.prob x * (W x).prob (y, z) = 0
    · exact Or.inr h
    · exact Or.inl (hs x y z h)
  simp only [hterm, Finset.sum_sub_distrib, Finset.mul_sum]

/-- `condDiv` against a degraded channel, in the support-compatible case. -/
lemma condDiv_eq_of_support (W : Channel X (Y × Z)) (V₁ : Channel Z Y) (pd : FinDist X)
    (hs : ∀ x y z, pd.prob x * (W x).prob (y, z) ≠ 0 → 0 < (V₁ z).prob y) :
    condDiv W (degradedChannel (eveMarginal W) V₁) pd =
      ((G W (fun z y => (V₁ z).prob y) pd.prob : ℝ) : EReal) := by
  unfold condDiv relEntropy
  rw [if_pos, D_sum W V₁ pd hs]
  intro t ht
  obtain ⟨x, y, z⟩ := t
  simp only [Function.mem_support, P_apply, Q_apply] at ht ⊢
  have hv := hs x y z ht
  have hw : 0 < (W x).prob (y, z) :=
    lt_of_le_of_ne ((W x).nonneg _) (fun h => ht (by rw [← h, mul_zero]))
  have hz : 0 < WZ W x z := lt_of_lt_of_le hw (W_le_WZ W x y z)
  have hp : pd.prob x ≠ 0 := fun h => ht (by rw [h, zero_mul])
  exact mul_ne_zero hp (mul_ne_zero hz.ne' hv.ne')

lemma sum_pW (W : Channel X (Y × Z)) (pd : FinDist X) :
    ∑ x, ∑ y, ∑ z, pd.prob x * (W x).prob (y, z) = 1 := by
  have : ∀ x, ∑ y, ∑ z, pd.prob x * (W x).prob (y, z) = pd.prob x := by
    intro x
    rw [← Fintype.sum_prod_type' (f := fun y z => pd.prob x * (W x).prob (y, z)), ← Finset.mul_sum,
      (W x).sum_eq_one, mul_one]
  simp only [this]
  exact pd.sum_eq_one

/-- Mixing with the uniform channel costs at most `log₂ 1/(1−t)`. -/
lemma mix_bound (W : Channel X (Y × Z)) (V₁ : Channel Z Y) (pd : FinDist X) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ((G W (fun z y => (1 - t) * (V₁ z).prob y + t / Fintype.card Y) pd.prob : ℝ) : EReal) ≤
      condDiv W (degradedChannel (eveMarginal W) V₁) pd + ((Real.logb 2 (1 / (1 - t)) : ℝ) : EReal) := by
  unfold condDiv relEntropy
  split_ifs with hs
  · rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    have hs' : ∀ x y z, pd.prob x * (W x).prob (y, z) ≠ 0 → 0 < (V₁ z).prob y := by
      intro x y z h
      have := hs (show (x, y, z) ∈ Function.support (jointLaw pd W).prob from h)
      simp only [Function.mem_support, Q_apply] at this
      have hne : (V₁ z).prob y ≠ 0 := fun h' => this (by rw [h', mul_zero, mul_zero])
      exact lt_of_le_of_ne ((V₁ z).nonneg y) (Ne.symm hne)
    rw [D_sum W V₁ pd hs']
    unfold G
    have hc : 0 ≤ Real.logb 2 (1 / (1 - t)) := Real.logb_nonneg (by norm_num)
      (by rw [le_div_iff₀ (by linarith)]; linarith)
    have hterm : ∀ x y z, pd.prob x * (W x).prob (y, z) * Real.logb 2 ((V₁ z).prob y) ≤
        pd.prob x * (W x).prob (y, z) * Real.logb 2 ((1 - t) * (V₁ z).prob y + t / Fintype.card Y) +
          pd.prob x * (W x).prob (y, z) * Real.logb 2 (1 / (1 - t)) := by
      intro x y z
      by_cases h0 : pd.prob x * (W x).prob (y, z) = 0
      · simp [h0]
      have hv := hs' x y z h0
      have hpw : 0 < pd.prob x * (W x).prob (y, z) :=
        lt_of_le_of_ne (mul_nonneg (pd.nonneg x) ((W x).nonneg _)) (Ne.symm h0)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hpw.le
      have hcard : (0 : ℝ) ≤ t / Fintype.card Y := by positivity
      have h1 : (1 - t) * (V₁ z).prob y ≤ (1 - t) * (V₁ z).prob y + t / Fintype.card Y := by
        linarith
      have h1t : 0 < 1 - t := by linarith
      have hpos : 0 < (1 - t) * (V₁ z).prob y := mul_pos h1t hv
      have h2 : Real.logb 2 ((1 - t) * (V₁ z).prob y) ≤
          Real.logb 2 ((1 - t) * (V₁ z).prob y + t / Fintype.card Y) :=
        Real.logb_le_logb_of_le (by norm_num) hpos h1
      rw [Real.logb_mul (by linarith) hv.ne', one_div, Real.logb_inv] at *
      linarith
    have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) =>
        Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => hterm x y z
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
    rw [sum_pW W pd, one_mul] at hsum
    linarith
  · rw [EReal.top_add_coe]
    exact le_top

/-! ### Sion's minimax theorem on full-support channels -/

/-- Channels with all transition probabilities at least `δ`. -/
def Xδ (Y Z : Type) [Fintype Y] (δ : ℝ) : Set (Z → Y → ℝ) :=
  {V | (∀ z y, δ ≤ V z y) ∧ ∀ z, ∑ y, V z y = 1}

/-- The probability simplex. -/
def Ys (X : Type) [Fintype X] : Set (X → ℝ) := {p | (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1}

lemma Xδ_convex (δ : ℝ) : Convex ℝ (Xδ Y Z δ) := by
  intro V hV U hU a b ha hb hab
  refine ⟨fun z y => ?_, fun z => ?_⟩
  · show δ ≤ a * V z y + b * U z y
    have h1 := mul_le_mul_of_nonneg_left (hV.1 z y) ha
    have h2 := mul_le_mul_of_nonneg_left (hU.1 z y) hb
    have h3 : a * δ + b * δ = δ := by rw [← add_mul, hab, one_mul]
    linarith
  · show ∑ y, (a * V z y + b * U z y) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hV.2 z, hU.2 z, mul_one,
      mul_one, hab]

lemma Ys_convex : Convex ℝ (Ys X) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun x => ?_, ?_⟩
  · show 0 ≤ a * p x + b * q x
    have := hp.1 x; have := hq.1 x
    positivity
  · show ∑ x, (a * p x + b * q x) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hq.2, mul_one, mul_one,
      hab]

lemma Xδ_compact (δ : ℝ) (hδ : 0 ≤ δ) : IsCompact (Xδ Y Z δ) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : Xδ Y Z δ = (⋂ z, ⋂ y, {V : Z → Y → ℝ | δ ≤ V z y}) ∩
        ⋂ z, {V : Z → Y → ℝ | ∑ y, V z y = 1} := by
      ext V; simp [Xδ]
    rw [h1]
    refine IsClosed.inter (isClosed_iInter fun z => isClosed_iInter fun y => ?_)
      (isClosed_iInter fun z => ?_)
    · exact isClosed_le continuous_const ((continuous_apply y).comp (continuous_apply z))
    · exact isClosed_eq (continuous_finsetSum _ fun y _ =>
        (continuous_apply y).comp (continuous_apply z)) continuous_const
  · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1, fun V hV => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun z => ?_
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun y => ?_
    rw [Real.norm_eq_abs, abs_le]
    have hnn : ∀ y', 0 ≤ V z y' := fun y' => hδ.trans (hV.1 z y')
    constructor
    · linarith [hnn y]
    · rw [← hV.2 z]
      exact Finset.single_le_sum (f := fun y' => V z y') (fun y' _ => hnn y') (Finset.mem_univ y)

lemma G_continuousOn (W : Channel X (Y × Z)) (δ : ℝ) (hδ : 0 < δ) (p : X → ℝ) :
    ContinuousOn (fun V => G W V p) (Xδ Y Z δ) := by
  unfold G
  refine continuousOn_const.sub (continuousOn_finsetSum _ fun x _ =>
    continuousOn_finsetSum _ fun y _ => continuousOn_finsetSum _ fun z _ => ?_)
  refine continuousOn_const.mul ?_
  unfold Real.logb
  refine ContinuousOn.div_const (ContinuousOn.log ?_ fun V hV => ?_) _
  · exact ((continuous_apply y).comp (continuous_apply z)).continuousOn
  · exact (lt_of_lt_of_le hδ (hV.1 z y)).ne'

lemma G_convexOn (W : Channel X (Y × Z)) (δ : ℝ) (hδ : 0 < δ) (p : X → ℝ) (hp : p ∈ Ys X) :
    ConvexOn ℝ (Xδ Y Z δ) (fun V => G W V p) := by
  have hlog : ∀ u v : ℝ, 0 < u → 0 < v → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a * Real.logb 2 u + b * Real.logb 2 v ≤ Real.logb 2 (a * u + b * v) := by
    intro u v hu hv a b ha hb hab
    have := strictConcaveOn_log_Ioi.concaveOn.2 (show u ∈ Set.Ioi (0:ℝ) from hu)
      (show v ∈ Set.Ioi (0:ℝ) from hv) ha hb hab
    simp only [smul_eq_mul] at this
    unfold Real.logb
    rw [mul_div_assoc', mul_div_assoc', ← add_div]
    exact div_le_div_of_nonneg_right this (Real.log_pos (by norm_num)).le
  refine ⟨Xδ_convex δ, fun V hV U hU a b ha hb hab => ?_⟩
  simp only [G, smul_eq_mul]
  have hterm : ∀ x y z, p x * (W x).prob (y, z) * (a * Real.logb 2 (V z y) +
      b * Real.logb 2 (U z y)) ≤ p x * (W x).prob (y, z) * Real.logb 2 ((a • V + b • U) z y) := by
    intro x y z
    have hw : 0 ≤ p x * (W x).prob (y, z) := mul_nonneg (hp.1 x) ((W x).nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hw
    have := hlog (V z y) (U z y) (lt_of_lt_of_le hδ (hV.1 z y)) (lt_of_lt_of_le hδ (hU.1 z y))
      a b ha hb hab
    simpa using this
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_le_sum fun y (_ : y ∈ Finset.univ) =>
      Finset.sum_le_sum fun z (_ : z ∈ Finset.univ) => hterm x y z
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have e1 : ∀ x y z, p x * (W x).prob (y, z) * (a * Real.logb 2 (V z y)) =
      a * (p x * (W x).prob (y, z) * Real.logb 2 (V z y)) := fun x y z => by ring
  have e2 : ∀ x y z, p x * (W x).prob (y, z) * (b * Real.logb 2 (U z y)) =
      b * (p x * (W x).prob (y, z) * Real.logb 2 (U z y)) := fun x y z => by ring
  simp only [e1, e2, ← Finset.mul_sum] at hsum
  have hconst : ∑ x, p x * Acoef W x = a * ∑ x, p x * Acoef W x + b * ∑ x, p x * Acoef W x := by
    rw [← add_mul, hab, one_mul]
  nlinarith [hsum, hconst]

lemma G_lin (W : Channel X (Y × Z)) (V : Z → Y → ℝ) (p q : X → ℝ) (a b : ℝ) :
    G W V (a • p + b • q) = a * G W V p + b * G W V q := by
  unfold G
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_sub,
    Finset.mul_sum]
  have e1 : ∀ x, a * p x * Acoef W x = a * (p x * Acoef W x) := fun x => by ring
  have e2 : ∀ x, b * q x * Acoef W x = b * (q x * Acoef W x) := fun x => by ring
  have e3 : ∀ x y z, a * p x * (W x).prob (y, z) * Real.logb 2 (V z y) =
      a * (p x * (W x).prob (y, z) * Real.logb 2 (V z y)) := fun x y z => by ring
  have e4 : ∀ x y z, b * q x * (W x).prob (y, z) * Real.logb 2 (V z y) =
      b * (q x * (W x).prob (y, z) * Real.logb 2 (V z y)) := fun x y z => by ring
  simp only [e1, e2, e3, e4]
  ring

lemma G_continuous_p (W : Channel X (Y × Z)) (V : Z → Y → ℝ) : Continuous (fun p => G W V p) := by
  unfold G
  refine (continuous_finsetSum _ fun x _ => (continuous_apply x).mul continuous_const).sub
    (continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ =>
      continuous_finsetSum _ fun z _ => ?_)
  exact ((continuous_apply x).mul continuous_const).mul continuous_const

lemma quasiconvexOn_coe {E : Type*} [AddCommMonoid E] [Module ℝ E] {s : Set E} {g : E → ℝ}
    (hg : ConvexOn ℝ s g) : QuasiconvexOn ℝ s (fun x => (g x : EReal)) := by
  rw [quasiconvexOn_iff_le_max]
  refine ⟨hg.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h1 := hg.2 hx hy ha hb hab
  have h2 : a • g x + b • g y ≤ max (g x) (g y) := by
    simp only [smul_eq_mul]
    have h4 := mul_le_mul_of_nonneg_left (le_max_left (g x) (g y)) ha
    have h5 := mul_le_mul_of_nonneg_left (le_max_right (g x) (g y)) hb
    have h6 : a * max (g x) (g y) + b * max (g x) (g y) = max (g x) (g y) := by
      rw [← add_mul, hab, one_mul]
    linarith
  have h3 : g (a • x + b • y) ≤ max (g x) (g y) := h1.trans h2
  calc ((g (a • x + b • y) : ℝ) : EReal) ≤ ((max (g x) (g y) : ℝ) : EReal) := by exact_mod_cast h3
    _ = max ((g x : ℝ) : EReal) ((g y : ℝ) : EReal) := by
        rcases le_total (g x) (g y) with h | h
        · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
        · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]

lemma quasiconcaveOn_coe {E : Type*} [AddCommMonoid E] [Module ℝ E] {s : Set E} {g : E → ℝ}
    (hg : ConcaveOn ℝ s g) : QuasiconcaveOn ℝ s (fun x => (g x : EReal)) := by
  rw [quasiconcaveOn_iff_min_le]
  refine ⟨hg.1, fun x hx y hy a b ha hb hab => ?_⟩
  have h1 := hg.2 hx hy ha hb hab
  have h2 : min (g x) (g y) ≤ a • g x + b • g y := by
    simp only [smul_eq_mul]
    have h4 := mul_le_mul_of_nonneg_left (min_le_left (g x) (g y)) ha
    have h5 := mul_le_mul_of_nonneg_left (min_le_right (g x) (g y)) hb
    have h6 : a * min (g x) (g y) + b * min (g x) (g y) = min (g x) (g y) := by
      rw [← add_mul, hab, one_mul]
    linarith
  have h3 : min (g x) (g y) ≤ g (a • x + b • y) := h2.trans h1
  calc min ((g x : ℝ) : EReal) ((g y : ℝ) : EReal) = ((min (g x) (g y) : ℝ) : EReal) := by
        rcases le_total (g x) (g y) with h | h
        · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
        · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
    _ ≤ ((g (a • x + b • y) : ℝ) : EReal) := by exact_mod_cast h3

/-- Sion's minimax theorem for the explicit objective on `δ`-full channels. -/
lemma sion (W : Channel X (Y × Z)) [Nonempty Y] (δ : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / Fintype.card Y) :
    (⨅ V ∈ Xδ Y Z δ, ⨆ p ∈ Ys X, ((G W V p : ℝ) : EReal)) =
      ⨆ p ∈ Ys X, ⨅ V ∈ Xδ Y Z δ, ((G W V p : ℝ) : EReal) := by
  have hcard : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  refine Sion.minimax' ?_ (Xδ_convex δ) (Xδ_compact δ hδ.le) ?_ ?_ Ys_convex ?_ ?_
  · refine ⟨fun _ _ => 1 / Fintype.card Y, fun z y => hδ1, fun z => ?_⟩
    simp [Finset.sum_const, Finset.card_univ]
  · intro p _
    exact (continuous_coe_real_ereal.comp_continuousOn (G_continuousOn W δ hδ p)).lowerSemicontinuousOn
  · intro p hp
    exact quasiconvexOn_coe (G_convexOn W δ hδ p hp)
  · intro V _
    exact (continuous_coe_real_ereal.comp (G_continuous_p W V)).continuousOn.upperSemicontinuousOn
  · intro V _
    refine quasiconcaveOn_coe ⟨Ys_convex, fun p _ q _ a b _ _ _ => ?_⟩
    rw [G_lin]
    simp

/-- Chain rule (inequality form): replacing `V₂` by Eve's true marginal never increases the
divergence, `D(P ‖ P_X W_Z V₁) ≤ D(P ‖ P_X V₂ V₁)`. -/
lemma chain_le (W : Channel X (Y × Z)) (V₂ : Channel X Z) (V₁ : Channel Z Y) (pd : FinDist X) :
    condDiv W (degradedChannel (eveMarginal W) V₁) pd ≤ condDiv W (degradedChannel V₂ V₁) pd := by
  have hQ2 : ∀ x y z, (jointLaw pd (degradedChannel V₂ V₁)).prob (x, y, z) =
      pd.prob x * ((V₂ x).prob z * (V₁ z).prob y) := fun _ _ _ => rfl
  unfold condDiv relEntropy
  split_ifs with h1 h2 h2
  · rw [EReal.coe_le_coe_iff]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    -- support facts
    have hsupp : ∀ x y z, pd.prob x * (W x).prob (y, z) ≠ 0 →
        0 < (V₂ x).prob z ∧ 0 < (V₁ z).prob y := by
      intro x y z h
      have := h2 (show (x, y, z) ∈ Function.support (jointLaw pd W).prob from h)
      simp only [Function.mem_support, hQ2] at this
      refine ⟨lt_of_le_of_ne ((V₂ x).nonneg z) (fun h' => this (by rw [← h']; ring)),
        lt_of_le_of_ne ((V₁ z).nonneg y) (fun h' => this (by rw [← h']; ring))⟩
    set e : X × Y × Z → ℝ := fun t => (pd.prob t.1 * (W t.1).prob t.2 -
      pd.prob t.1 * (W t.1).prob t.2 * ((V₂ t.1).prob t.2.2 / WZ W t.1 t.2.2)) / Real.log 2 with he
    have hterm : ∀ t, e t ≤ (jointLaw pd W).prob t * Real.logb 2 ((jointLaw pd W).prob t /
        (jointLaw pd (degradedChannel V₂ V₁)).prob t) -
        (jointLaw pd W).prob t * Real.logb 2 ((jointLaw pd W).prob t /
        (jointLaw pd (degradedChannel (eveMarginal W) V₁)).prob t) := by
      intro t
      obtain ⟨x, y, z⟩ := t
      rw [P_apply, hQ2, Q_apply]
      by_cases h0 : pd.prob x * (W x).prob (y, z) = 0
      · simp [he, h0]
      obtain ⟨hv2, hv1⟩ := hsupp x y z h0
      have hp : 0 < pd.prob x := lt_of_le_of_ne (pd.nonneg x) (fun h => h0 (by rw [← h, zero_mul]))
      have hw : 0 < (W x).prob (y, z) :=
        lt_of_le_of_ne ((W x).nonneg _) (fun h => h0 (by rw [← h, mul_zero]))
      have hz : 0 < WZ W x z := lt_of_lt_of_le hw (W_le_WZ W x y z)
      have key : Real.logb 2 (pd.prob x * (W x).prob (y, z) /
            (pd.prob x * ((V₂ x).prob z * (V₁ z).prob y))) -
          Real.logb 2 (pd.prob x * (W x).prob (y, z) / (pd.prob x * (WZ W x z * (V₁ z).prob y))) =
          Real.logb 2 (WZ W x z / (V₂ x).prob z) := by
        have e1 : Real.logb 2 (pd.prob x * ((V₂ x).prob z * (V₁ z).prob y)) =
            Real.logb 2 (pd.prob x) + Real.logb 2 ((V₂ x).prob z) + Real.logb 2 ((V₁ z).prob y) := by
          rw [Real.logb_mul hp.ne' (by positivity), Real.logb_mul hv2.ne' hv1.ne']; ring
        have e2 : Real.logb 2 (pd.prob x * (WZ W x z * (V₁ z).prob y)) =
            Real.logb 2 (pd.prob x) + Real.logb 2 (WZ W x z) + Real.logb 2 ((V₁ z).prob y) := by
          rw [Real.logb_mul hp.ne' (by positivity), Real.logb_mul hz.ne' hv1.ne']; ring
        have e3 : Real.logb 2 (pd.prob x * (W x).prob (y, z)) =
            Real.logb 2 (pd.prob x) + Real.logb 2 ((W x).prob (y, z)) :=
          Real.logb_mul hp.ne' hw.ne'
        rw [Real.logb_div (by positivity) (by positivity), Real.logb_div (by positivity)
          (by positivity), Real.logb_div hz.ne' hv2.ne', e1, e2, e3]
        ring
      have hlb : (1 - (V₂ x).prob z / WZ W x z) / Real.log 2 ≤
          Real.logb 2 (WZ W x z / (V₂ x).prob z) := by
        unfold Real.logb
        rw [div_le_div_iff_of_pos_right hlog2]
        have := Real.one_sub_inv_le_log_of_pos (show 0 < WZ W x z / (V₂ x).prob z by positivity)
        rwa [inv_div] at this
      have hpw : 0 < pd.prob x * (W x).prob (y, z) := mul_pos hp hw
      simp only [he]
      rw [← mul_sub, key]
      calc (pd.prob x * (W x).prob (y, z) - pd.prob x * (W x).prob (y, z) *
            ((V₂ x).prob z / WZ W x z)) / Real.log 2
          = pd.prob x * (W x).prob (y, z) * ((1 - (V₂ x).prob z / WZ W x z) / Real.log 2) := by
            ring
        _ ≤ _ := by gcongr
    have hsum_e : 0 ≤ ∑ t, e t := by
      simp only [he, ← Finset.sum_div]
      refine div_nonneg ?_ hlog2.le
      rw [Finset.sum_sub_distrib, sub_nonneg]
      have h1' : ∑ t : X × Y × Z, pd.prob t.1 * (W t.1).prob t.2 = 1 := by
        rw [Fintype.sum_prod_type]
        simp only [← Finset.mul_sum, (W _).sum_eq_one, mul_one]
        exact pd.sum_eq_one
      rw [h1']
      have h2' : ∑ t : X × Y × Z, pd.prob t.1 * (W t.1).prob t.2 * ((V₂ t.1).prob t.2.2 /
          WZ W t.1 t.2.2) = ∑ x, ∑ z, pd.prob x * WZ W x z * ((V₂ x).prob z / WZ W x z) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        simp only
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        rfl
      rw [h2']
      calc ∑ x, ∑ z, pd.prob x * WZ W x z * ((V₂ x).prob z / WZ W x z)
          ≤ ∑ x, ∑ z, pd.prob x * (V₂ x).prob z := by
            refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => ?_
            by_cases hz : WZ W x z = 0
            · rw [hz, mul_zero, zero_mul]; exact mul_nonneg (pd.nonneg x) ((V₂ x).nonneg z)
            · rw [mul_assoc, mul_div_cancel₀ _ hz]
        _ = 1 := by
            simp only [← Finset.mul_sum, (V₂ _).sum_eq_one, mul_one]
            exact pd.sum_eq_one
    have := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => hterm t
    rw [Finset.sum_sub_distrib] at this
    linarith
  · exact le_top
  · exfalso
    apply h1
    intro t ht
    obtain ⟨x, y, z⟩ := t
    have := h2 ht
    simp only [Function.mem_support, hQ2] at this
    simp only [Function.mem_support, Q_apply]
    simp only [Function.mem_support, P_apply] at ht
    have hw : 0 < (W x).prob (y, z) :=
      lt_of_le_of_ne ((W x).nonneg _) (fun h => ht (by rw [← h, mul_zero]))
    have hz : 0 < WZ W x z := lt_of_lt_of_le hw (W_le_WZ W x y z)
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact this (by rw [h, zero_mul])
    · rcases mul_eq_zero.mp h with h' | h'
      · exact hz.ne' h'
      · exact this (by rw [h', mul_zero, mul_zero])
  · exact le_top

lemma ereal_le_of_forall_add (a b : EReal) (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) : a ≤ b := by
  induction b using EReal.rec with
  | bot =>
    have := h 1 one_pos
    rwa [EReal.bot_add] at this
  | top => exact le_top
  | coe r =>
    induction a using EReal.rec with
    | bot => exact bot_le
    | top =>
      have := h 1 one_pos
      rw [← EReal.coe_add] at this
      exact absurd this (not_le.mpr (EReal.coe_lt_top _))
    | coe s =>
      rw [EReal.coe_le_coe_iff]
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := h ε hε
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at this
      exact this

end MinimaxAux

open MinimaxAux CondDivAux in
theorem solution {X Y Z : Type} [Fintype X] [Nonempty X] [Fintype Y] [Fintype Z]
    (W : WildeQIT.Channel X (Y × Z)) :
    ((⨅ (V₂ : WildeQIT.Channel X Z) (V₁ : WildeQIT.Channel Z Y),
        ⨆ p : WildeQIT.FinDist X, WiretapFeedback.condDiv W (WiretapFeedback.degradedChannel V₂ V₁) p) =
      ⨅ V₁ : WildeQIT.Channel Z Y,
        ⨆ p : WildeQIT.FinDist X, WiretapFeedback.condDiv W
          (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) V₁) p) ∧
    ((⨅ V₁ : WildeQIT.Channel Z Y,
        ⨆ p : WildeQIT.FinDist X, WiretapFeedback.condDiv W
          (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) V₁) p) =
      ⨆ p : WildeQIT.FinDist X,
        ⨅ V₁ : WildeQIT.Channel Z Y, WiretapFeedback.condDiv W
          (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) V₁) p) ∧
    ((⨆ p : WildeQIT.FinDist X,
        ⨅ V₁ : WildeQIT.Channel Z Y, WiretapFeedback.condDiv W
          (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) V₁) p) =
      ⨆ p : WildeQIT.FinDist X, WildeQIT.relEntropy (WiretapFeedback.jointLaw p W)
        (fun t => (WiretapFeedback.jointLaw p W).margXZ.prob (t.1, t.2.2) *
          (WiretapFeedback.jointLaw p W).margYZ.prob t.2 /
          (WiretapFeedback.jointLaw p W).margYZ.snd.prob t.2.2)) ∧
    ((⨆ p : WildeQIT.FinDist X, WildeQIT.relEntropy (WiretapFeedback.jointLaw p W)
        (fun t => (WiretapFeedback.jointLaw p W).margXZ.prob (t.1, t.2.2) *
          (WiretapFeedback.jointLaw p W).margYZ.prob t.2 /
          (WiretapFeedback.jointLaw p W).margYZ.snd.prob t.2.2)) =
      ⨆ p : WildeQIT.FinDist X,
        ((WildeQIT.condMutualInfo (WiretapFeedback.jointLaw p W) : ℝ) : EReal)) := by
  have hcond : ∀ p : WildeQIT.FinDist X,
      (⨅ V₁ : WildeQIT.Channel Z Y, WiretapFeedback.condDiv W
          (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) V₁) p) =
        WildeQIT.relEntropy (WiretapFeedback.jointLaw p W) (Qs (WiretapFeedback.jointLaw p W)) ∧
      WildeQIT.relEntropy (WiretapFeedback.jointLaw p W) (Qs (WiretapFeedback.jointLaw p W)) =
        ((WildeQIT.condMutualInfo (WiretapFeedback.jointLaw p W) : ℝ) : EReal) :=
    fun p => WiretapFeedback.iInf_condDiv_eq_condMutualInfo W p
  refine ⟨?_, ?_, iSup_congr fun p => (hcond p).1, iSup_congr fun p => (hcond p).2⟩
  · -- conjunct 1: the chain rule
    apply le_antisymm
    · exact le_iInf fun V₁ => iInf_le_of_le (WiretapFeedback.eveMarginal W) (iInf_le _ V₁)
    · exact le_iInf fun V₂ => le_iInf fun V₁ =>
        iInf_le_of_le V₁ (iSup_mono fun p => chain_le W V₂ V₁ p)
  · -- conjunct 2: minimax
    apply le_antisymm
    swap
    · exact iSup_iInf_le_iInf_iSup (fun p V₁ => WiretapFeedback.condDiv W
        (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) V₁) p)
    obtain ⟨x0⟩ := ‹Nonempty X›
    have hY : Nonempty Y := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := (W x0).sum_eq_one
      simp at this
    have hcard : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
    refine ereal_le_of_forall_add _ _ fun ε hε => ?_
    set t : ℝ := 1 - (2 : ℝ) ^ (-ε) with ht
    have h2ε : (2 : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have h2ε' : 0 < (2 : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by norm_num) _
    have ht0 : 0 < t := by rw [ht]; linarith
    have ht1 : t < 1 := by rw [ht]; linarith
    have hc : Real.logb 2 (1 / (1 - t)) = ε := by
      rw [ht, sub_sub_cancel, one_div, ← Real.rpow_neg (by norm_num), neg_neg,
        Real.logb_rpow (by norm_num) (by norm_num)]
    set δ : ℝ := t / Fintype.card Y with hδ
    have hδ0 : 0 < δ := div_pos ht0 hcard
    have hδ1 : δ ≤ 1 / Fintype.card Y := by
      rw [hδ]; exact div_le_div_of_nonneg_right ht1.le hcard.le
    calc (⨅ V₁ : WildeQIT.Channel Z Y, ⨆ p : WildeQIT.FinDist X, WiretapFeedback.condDiv W
          (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) V₁) p)
        ≤ ⨅ V ∈ Xδ Y Z δ, ⨆ q ∈ Ys X, ((G W V q : ℝ) : EReal) := by
          refine le_iInf₂ fun V hV => ?_
          let chan : WildeQIT.Channel Z Y := fun z =>
            { prob := fun y => V z y
              nonneg := fun y => hδ0.le.trans (hV.1 z y)
              sum_eq_one := hV.2 z }
          refine iInf_le_of_le chan (iSup_le fun pd => ?_)
          rw [condDiv_eq_of_support W chan pd (fun x y z _ => lt_of_lt_of_le hδ0 (hV.1 z y))]
          exact le_iSup₂_of_le (f := fun q (_ : q ∈ Ys X) => ((G W V q : ℝ) : EReal)) pd.prob
            ⟨pd.nonneg, pd.sum_eq_one⟩ le_rfl
      _ = ⨆ q ∈ Ys X, ⨅ V ∈ Xδ Y Z δ, ((G W V q : ℝ) : EReal) := sion W δ hδ0 hδ1
      _ ≤ _ := by
          refine iSup₂_le fun q hq => ?_
          let pd : WildeQIT.FinDist X := ⟨q, hq.1, hq.2⟩
          obtain ⟨Vs, hVs⟩ := exists_opt W pd
          have hmem : (fun z y => (1 - t) * (Vs z).prob y + t / Fintype.card Y) ∈ Xδ Y Z δ := by
            refine ⟨fun z y => ?_, fun z => ?_⟩
            · have := mul_nonneg (sub_nonneg.mpr ht1.le) ((Vs z).nonneg y)
              rw [hδ]; linarith
            · rw [Finset.sum_add_distrib, ← Finset.mul_sum, (Vs z).sum_eq_one, mul_one,
                Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              field_simp
              ring
          calc (⨅ V ∈ Xδ Y Z δ, ((G W V q : ℝ) : EReal))
              ≤ ((G W (fun z y => (1 - t) * (Vs z).prob y + t / Fintype.card Y) q : ℝ) : EReal) :=
                iInf₂_le _ hmem
            _ ≤ WiretapFeedback.condDiv W
                (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) Vs) pd +
                ((Real.logb 2 (1 / (1 - t)) : ℝ) : EReal) := mix_bound W Vs pd t ht0 ht1
            _ ≤ _ := by
                rw [hc, hVs, ← (hcond pd).1]
                gcongr
                exact le_iSup (fun p : WildeQIT.FinDist X => ⨅ V₁ : WildeQIT.Channel Z Y,
                  WiretapFeedback.condDiv W
                    (WiretapFeedback.degradedChannel (WiretapFeedback.eveMarginal W) V₁) p) pd
