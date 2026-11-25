-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.vol_std_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:45.975809+00:00
-- url     : https://prove2.me/submissions/c5b3b4bb-1f06-47aa-b0d9-ea66843b4868

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_algebraMap_thetaO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    (hok : UnitDetRootDefs.CmOK a b c d) {m : Type} [Fintype m] [DecidableEq m] :
    vol (KF b d) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≤ Submodule.span (𝓞 (KF b d)) {lam ^ Fintype.card m} := by
  unfold vol volSet UnitDetRootDefs.stdLat
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  have h1 : ∀ j i, v j i ∈ (UnitDetRootDefs.cmL a b d ha hd lam hlam).lattice :=
    fun j i => (show ∀ i ∈ (Set.univ : Set m), v j i ∈ _ from hv j) i (Set.mem_univ i)
  clear hv
  have hent : ∀ j i, ∃ o : 𝓞 (KF b d), v j i = lam * algebraMap (𝓞 (KF b d)) ℂ o := by
    intro j i
    have h2 := h1 j i
    simp only [PeriodPair.lattice, UnitDetRootDefs.cmL, UnitDetRootDefs.scalePair,
      UnitDetRootDefs.cmPair] at h2
    obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp h2
    refine ⟨p * (a : 𝓞 (KF b d)) + q * thetaO hok, ?_⟩
    rw [← hpq]
    simp only [map_add, map_mul, algebraMap_thetaO, map_intCast, map_natCast, zsmul_eq_mul]
    ring
  choose o ho using hent
  have hM : Matrix.of v = lam • (algebraMap (𝓞 (KF b d)) ℂ).mapMatrix (Matrix.of o) := by
    ext j i
    simp [ho j i]
  rw [hM, Matrix.det_smul, ← RingHom.map_det]
  refine Submodule.mem_span_singleton.mpr ⟨(Matrix.of o).det, ?_⟩
  rw [Algebra.smul_def, mul_comm]
end PI.UnitaryGroupMassFormula.UnitDetRoot
