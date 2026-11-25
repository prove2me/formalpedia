-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_quotLaurent_finite_53e2c0015aff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:07:22.031564+00:00
-- url     : https://prove2.me/submissions/86a525c9-00b9-437a-a467-f7d48af5ef1c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StepTwoFiltGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
variable {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
variable (M₁ M₂ : FinGradedSub (S := S) (x := x) E)
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : Module.Finite (Poly S N) (quotLaurent M₁ M₂) := by
  classical
  obtain ⟨n, deg, gen, hgen, hspan⟩ := M₁.fg
  have hfg : M₁.laurent.FG := by
    refine ⟨Finset.univ.image fun j => laurentSingle x (deg j) (gen j), le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro _ hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_coe.mp hz |> Finset.mem_image.mp
      exact laurentSingle_mem (hgen j)
    · intro m hm
      rw [← (Finsupp.sum_single m)]
      refine Submodule.sum_mem _ fun c _ => ?_
      have h1 : Submodule.span S {z | ∃ (j : Fin n) (f : Poly S N) (e : ℕ),
          f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f • gen j} ≤
          ((Submodule.span (Poly S N) ((Finset.univ.image fun j => laurentSingle x (deg j) (gen j) :
            Finset (LaurentSpace x E)) : Set (LaurentSpace x E))).restrictScalars S).comap
            (Finsupp.lsingle c) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, f, e, hf, rfl, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.restrictScalars_mem, Finsupp.lsingle_apply]
        change laurentSingle x _ _ ∈ _
        rw [add_comm (e : ℤ) (deg j), ← laurent_smul_single hf]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr
          (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
      exact h1 (hspan c (hm c))
  have : Module.Finite (Poly S N) M₁.laurent := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
end GroundTheory.Heights₂.Heights.Kleiman
