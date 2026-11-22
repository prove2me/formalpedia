-- Prove2me | solution 1 for QECCertificates.LRAT.le_minWeight_of_unsat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:10.449373+00:00
-- url     : https://prove2.me/submissions/94e094de-8587-4d9d-a409-efe8b3d2513f

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Distance
public import Theorems.Thm_QECCertificates_LRAT_no_light_logical_of_unsat
public import Theorems.Thm_QECCertificates_le_minWeight_of_lower
public import Theorems.Thm_QECCertificates_weight_eq_hammingNorm


set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT
namespace QECCertificates.LRAT
theorem _root_.solution {n k : ℕ} {Rker Rpair : List (List Nat)}
    {m₁ m₂ : ℕ} (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {F : CNF}
    (hF : buildPair Rker Rpair n k = F) (hunsat : ¬ Satisfiable F) (hn : 0 < n)
    (hne₁ : ∀ r ∈ Rker, r ≠ []) (hne₂ : ∀ r ∈ Rpair, r ≠ [])
    (hb₁ : ∀ r ∈ Rker, ∀ t ∈ r, t < n) (hb₂ : ∀ r ∈ Rpair, ∀ t ∈ r, t < n)
    (hd₁ : ∀ r ∈ Rker, r.Nodup) (hd₂ : ∀ r ∈ Rpair, r.Nodup)
    (hrow₁ : Rker.map (rowOf n) = List.ofFn fun i => M₁ i)
    (hrow₂ : Rpair.map (rowOf n) = List.ofFn fun i => M₂ i)
    (hk : k + 1 ≤ n) : k + 1 ≤ minWeightKernelOutsideRowSpace M₁ M₂ := by
  apply le_minWeight_of_lower M₁ M₂ hk
  intro E hker hnot
  by_contra hlt
  have hw : (support E).card ≤ k := by
    rw [weight_eq_hammingNorm]
    omega
  exact no_light_logical_of_unsat M₁ M₂ hF hunsat hn hne₁ hne₂ hb₁ hb₂ hd₁ hd₂
    hrow₁ hrow₂ ⟨E, hw, hker, hnot⟩
end QECCertificates.LRAT
