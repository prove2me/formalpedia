-- Prove2me | solution 1 for PI.VolStabSW.OmFibG.dxOpen_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:39:55.118315+00:00
-- url     : https://prove2.me/submissions/f4b7cc2a-f06d-4d8a-81e0-d1b1b6a41e7a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_FibExGram
import Theorems.Thm_PI_VolStabSW_HasDens_sub
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabSW_gramB_add_right
import Theorems.Thm_PI_VolStabSW_gramR_add_sub
import Theorems.Thm_PI_VolStabSW_isReduced_tens_field
import Theorems.Thm_PI_VolStabSW_secGram_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.OmFibG
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct
namespace PI.VolStabSW.OmFibG
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (a : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (d : ℕ) (b : Module.Basis (Fin d) F E) (x : Fin a → Fin M → Fv F v ⊗[F] E)
    (hx : LinearIndependent (Fv F v ⊗[F] E) x) :
    IsOpen ((fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x -
      gramH (Fv F v) σ hσ J hJ W) '' (latSub b v a M : Set (Fin a → Fin M → Fv F v ⊗[F] E))) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)
  have : IsReduced (Fv F v ⊗[F] E) := isReduced_tens_field F E (Fv F v)
  have hss : IsSemisimpleRing (Fv F v ⊗[F] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  obtain ⟨q, hq⟩ := secGram_holds F E σ hσ M J hJ hdet (Fv F v) hss a x hx
  set T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun S j k => ∑ i', (algebraMap F (Fv F v ⊗[F] E) (1 / 2) * S i' j) * q k i' with hT
  have hTc : Continuous T := by
    refine continuous_pi fun j => continuous_pi fun k => continuous_finsetSum _ fun i' _ => ?_
    exact (continuous_const.mul (continuous_id.matrix_elem i' j)).mul continuous_const
  have hT0 : T 0 = 0 := by
    funext j k
    simp [hT]
  set L := latSub b v a M with hL
  have hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    (PositiveNearLattice.isClopen_latV b v a M).isOpen
  set Dx : (Fin a → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ a := fun W =>
    gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x - gramH (Fv F v) σ hσ J hJ W
    with hDx
  have hDB : ∀ W, (Dx W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramB (Fv F v) σ J x W := by
    intro W
    rw [← gramR_add_sub]
    rfl
  have hDadd : ∀ W W', Dx (W + W') = Dx W + Dx W' := by
    intro W W'
    apply Subtype.ext
    rw [AddSubgroup.coe_add, hDB, hDB, hDB, gramB_add_right]
  have hDT : ∀ S : HermR (Fv F v) σ a, Dx (T S) = S := by
    intro S
    apply Subtype.ext
    rw [hDB]
    exact hq S.1 S.2
  show IsOpen (Dx '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨l, hl, rfl⟩
  have hU : IsOpen {S : HermR (Fv F v) σ a | T ((S - Dx l : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L} :=
    hLo.preimage (hTc.comp (continuous_subtype_val.comp (continuous_id.sub continuous_const)))
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · show T ((Dx l - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L
    rw [sub_self, AddSubgroup.coe_zero, hT0]
    exact L.zero_mem
  · intro S hS
    refine ⟨l + T ((S - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)),
      L.add_mem hl hS, ?_⟩
    rw [hDadd, hDT]
    abel
end PI.VolStabSW.OmFibG
