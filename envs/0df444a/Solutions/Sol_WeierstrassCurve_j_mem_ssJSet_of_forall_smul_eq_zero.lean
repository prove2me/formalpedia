-- Prove2me | solution 1 for WeierstrassCurve.j_mem_ssJSet_of_forall_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/fece17cd-7249-5eed-b1dc-0bc172854d04

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_WeierstrassCurve_exists_addEquiv_point_variableChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_j_mem_ssJSet_of_forall_smul_eq_zero

set_option autoImplicit false

namespace P2SSTransport

open WeierstrassCurve

theorem forall_smul_eq_zero_of_addEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (n : ℕ) (hB : ∀ Q : B, n • Q = 0 → Q = 0) :
    ∀ P : A, n • P = 0 → P = 0 := by
  intro P hP
  have h1 : n • e P = 0 := by
    rw [← map_nsmul, hP, map_zero]
  have h2 : e P = 0 := hB _ h1
  exact (map_eq_zero_iff e e.injective).mp h2

theorem forall_smul_eq_zero_of_variableChange {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) (C : VariableChange K) (n : ℕ)
    (h : ∀ Q : (C • W).toAffine.Point, n • Q = 0 → Q = 0) :
    ∀ P : W.toAffine.Point, n • P = 0 → P = 0 := by
  obtain ⟨e, -⟩ := WeierstrassCurve.exists_addEquiv_point_variableChange W C
  exact forall_smul_eq_zero_of_addEquiv e n h

end P2SSTransport

theorem solution {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q' : ℕ) [Fact q'.Prime] [CharP κ q'] (W : WeierstrassCurve κ) [W.IsElliptic]
    (hss : ∀ P : W.toAffine.Point, q' • P = 0 → P = 0) :
    W.j ∈ ModularCurve.ssJSet q' κ := by
  rw [ModularCurve.mem_ssJSet_iff]
  intro W' _ hj

  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W' W hj
  subst hC
  exact P2SSTransport.forall_smul_eq_zero_of_variableChange W' C q' hss

end S_WeierstrassCurve_j_mem_ssJSet_of_forall_smul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_j_mem_ssJSet_of_forall_smul_eq_zero (solution)
