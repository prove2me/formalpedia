-- Prove2me | solution 1 for PI.VolStabW.VolAAW.ev_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:38.047523+00:00
-- url     : https://prove2.me/submissions/4491f0f1-186d-42af-9066-98da10c47fde

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensVolB
import Theorems.Thm_PI_VolStabW_VolAAW_BR_eT_left
import Theorems.Thm_PI_VolStabW_VolAAW_BR_eq_sum
import Theorems.Thm_PI_VolStabW_VolAAW_mem_latV_iff
import Theorems.Thm_PI_VolStabW_VolAAW_mulVec_int
import Theorems.Thm_PI_VolStabW_VolAAW_det_gG
import Theorems.Thm_PI_VolStabW_SdDualW_eT_mem
import Theorems.Thm_PI_VolStabW_VolAAW_ev_int_all


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.VolAAW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW
  PositiveNearLattice SdDualW
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.VolAAW
theorem _root_.solution [Algebra.IsSeparable F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) :
    ∀ᶠ v in cofinite, {Y | ∀ X ∈ latV (M := M) (n := a) b v,
      BR (Fv F v) σ J X Y ∈ v.adicCompletionIntegers F} = latV (M := M) (n := a) b v := by
  classical
  filter_upwards [ev_int_all (fun q : (Fin a × Fin M × Fin d) × (Fin a × Fin M × Fin d) =>
      gG b σ J a q.1 q.2),
    ev_int_all (fun q : (Fin a × Fin M × Fin d) × (Fin a × Fin M × Fin d) =>
      (gG b σ J a)⁻¹ q.1 q.2)] with v h1 h2
  have hdet := det_gG b v σ hσ J hJ (a := a)
  set g := gG b σ J a with hg
  ext Y
  constructor
  · intro hY
    rw [Set.mem_setOf_eq] at hY
    rw [mem_latV_iff]
    have hw : ∀ q, (g.map (algebraMap F (Fv F v))).mulVec (cT b v Y) q ∈
        v.adicCompletionIntegers F := by
      intro q
      rw [← BR_eT_left]
      exact hY _ (eT_mem v b q)
    have hinv : (g⁻¹.map (algebraMap F (Fv F v))).mulVec
        ((g.map (algebraMap F (Fv F v))).mulVec (cT b v Y)) = cT b v Y := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul g (isUnit_iff_ne_zero.2 hdet), Matrix.map_one _ (map_zero _)
        (map_one _), Matrix.one_mulVec]
    intro q
    rw [← hinv]
    exact mulVec_int v g⁻¹ (fun i j => h2 (i, j)) _ hw q
  · intro hY
    rw [Set.mem_setOf_eq]
    intro X hX
    rw [BR_eq_sum]
    rw [mem_latV_iff] at hX hY
    exact sum_mem fun q _ => mul_mem (hX q) (mulVec_int v g (fun i j => h1 (i, j)) _ hY q)
end PI.VolStabW.VolAAW
