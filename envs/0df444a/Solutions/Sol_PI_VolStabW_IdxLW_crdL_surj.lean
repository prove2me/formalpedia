-- Prove2me | solution 1 for PI.VolStabW.IdxLW.crdL_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:20.359432+00:00
-- url     : https://prove2.me/submissions/681d9b4a-f4cc-40b9-a45d-965d3f40423d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Definitions.Def_ReciprocityTheory_ResidueCardinality_ArtinOntoB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHIL

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
open PI.VolStabW.IdxLW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (a M : ℕ)
namespace PI.VolStabW.IdxLW
theorem _root_.solution : Function.Surjective (crdL v b a M) := by
  intro c
  let x : Fin a → Fin M → Fv F v ⊗[F] E := fun i j =>
    (Algebra.TensorProduct.basis (Fv F v) b).repr.symm
      (Finsupp.equivFunOnFinite.symm fun k => (c (i, j, k) : Fv F v))
  have hx : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x i j) k = c (i, j, k) := by
    intro i j k
    simp [x]
  refine ⟨⟨x, fun i j k => by rw [hx]; exact (c (i, j, k)).2⟩, ?_⟩
  funext q
  apply Subtype.ext
  exact hx q.1 q.2.1 q.2.2
end PI.VolStabW.IdxLW
