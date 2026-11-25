-- Prove2me | solution 1 for PI.LevelKSplit.W.NC.ncoord_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:28.547613+00:00
-- url     : https://prove2.me/submissions/672a6426-bc5f-4587-a2f2-470a23f7dc8f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CoordinateHomeomorphism
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfSemiNHSHeisLev
import Theorems.Thm_PI_LevelKSplit_W_NC_isClosed_FixXp
import Theorems.Thm_PI_LevelKSplit_W_ExC_isClosed_Nsub
import Theorems.Thm_PI_LevelKSplit_W_NC_cHomeo_apply
import Theorems.Thm_PI_LevelKSplit_W_NC_coord_skew


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} [FiniteDimensional F E]
namespace PI.LevelKSplit.W.NC
theorem _root_.solution (hH : HeisP F E σ M J) (hL : LevP F E σ M J) : NCoord F E σ M J := by
  intro hJ hinv r P T hP
  obtain ⟨sH, csH, cyH, hs1, hdec, hyH, hZN1, hcent, hmul, hZnorm, hconj, hZconj⟩ :=
    hH hJ hinv r P T hP
  obtain ⟨A, Lev, hAN, hAcl, cLev, hLev, hAN1, hN1norm, hAcomm⟩ := hL hJ hinv r P T hP
  have hmemW : ∀ m : LevelUnipotentSubgroup (Af F) σ J P, ∀ a, yH (Af F) σ J P m a ∈ Wp (Af F) σ J P := by
    intro m a
    obtain ⟨y, hy, -⟩ := hdec m m.2
    rw [← hy a]; exact (y a).2
  let yQ : LevelUnipotentSubgroup (Af F) σ J P → (Fin r → Wp (Af F) σ J P) := fun m a =>
    ⟨yH (Af F) σ J P m a, hmemW m a⟩
  have H : CoordHyp (Nsub (Af F) σ J P) A (LevelUnipotentSubgroup (Af F) σ J P) (Zsub (Af F) σ J P) Lev sH yQ :=
    { hAN := hAN
      coordinate_level_le := inf_le_left
      hZN1 := hZN1
      cLev := cLev
      csH := csH
      cyQ := continuous_pi fun a => Continuous.subtype_mk
        ((continuous_apply a).comp (cyH.comp continuous_subtype_val)) _
      lev_mem := fun n hn => (hLev n hn).1
      lev_rest := fun n hn => (hLev n hn).2
      triv := hAN1
      norm1 := hN1norm
      sH_mem := hs1
      dec := fun m => by
        obtain ⟨y, hy, hz⟩ := hdec m m.2
        have : yQ m = y := funext fun a => Subtype.ext (hy a).symm
        rw [this]; exact hz
      yQ_sH := fun y z hz => funext fun a => Subtype.ext (hyH y z hz a)
      cent := hcent
      mul := hmul }
  refine ⟨A, Zsub (Af F) σ J P, cHomeo H, hAcl, ?_, fun n0 => coord_skew H n0, ?_⟩
  · show IsClosed ((Nsub (Af F) σ J P ⊓ FixXp (Af F) σ J P : Subgroup (HA (Af F) σ J)) :
      Set (HA (Af F) σ J))
    rw [Subgroup.coe_inf]
    exact (ExC.isClosed_Nsub hJ hinv P T hP).inter (isClosed_FixXp P)
  · intro h hh u y z
    obtain ⟨y', hy', hc⟩ := hconj h hh y
    refine ⟨y', hy', ?_⟩
    rw [cHomeo_apply, cHomeo_apply]
    have hu : h * (u : HA (Af F) σ J) * h⁻¹ = u := by rw [hAcomm h hh u u.2]; group
    have hz : h * (z : HA (Af F) σ J) * h⁻¹ = z := hZconj h hh z z.2
    calc h * ((u : HA (Af F) σ J) * sH y * (z : HA (Af F) σ J)) * h⁻¹
        = (h * u * h⁻¹) * (h * sH y * h⁻¹) * (h * z * h⁻¹) := by group
      _ = u * sH y' * z := by rw [hu, hc, hz]
end PI.LevelKSplit.W.NC
