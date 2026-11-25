-- Prove2me | solution 1 for PI.LocLatEq.W.latL_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:57:17.120631+00:00
-- url     : https://prove2.me/submissions/d0a66f30-3e31-4833-bbcb-1a4446f0d2e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatEq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeEquality_Development
import Theorems.Thm_PI_LocLatEq_W_bc_smul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
open PI PI.LocLatEq PI.LocLatEq.W
namespace PI.LocLatEq.W
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (hU : UnitP)
    (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ x ∈ Λ, ∃ d : 𝓞 F, d ∉ p.asIdeal ∧ algebraMap (𝓞 F) (𝓞 E) d • x ∈ Λ') :
    latL A Λ ≤ latL A Λ' := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨d, hd, hdx⟩ := h x hx
  obtain ⟨u, hu, hu1⟩ := hU F E sig p A d hd
  have hmem : ((⟨u, hu⟩ : A.O) • bc A (algebraMap (𝓞 F) (𝓞 E) d • x)) ∈ latL A Λ' :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hdx, rfl⟩)
  have heq : (⟨u, hu⟩ : A.O) • bc A (algebraMap (𝓞 F) (𝓞 E) d • x) = bc A x := by
    rw [Subring.smul_def, bc_smul, smul_smul]
    simp only [hu1, one_smul]
  rw [SetLike.mem_coe, ← heq]
  exact hmem
end PI.LocLatEq.W
