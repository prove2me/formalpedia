-- Prove2me | solution 1 for OrderClosures.solovayA_mem_of_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:02.331652+00:00
-- url     : https://prove2.me/submissions/b0e1c96e-065e-4f6e-8d61-b76ca0abe821

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
public import Theorems.Thm_OrderClosures_IsCompleteBooleanSubalgebra_sInf_mem
public import Theorems.Thm_OrderClosures_solovayLT_eq_sSup
public import Theorems.Thm_OrderClosures_solovayStrict_eq
public import Theorems.Thm_OrderClosures_solovayNotLT_eq
public import Theorems.Thm_OrderClosures_solovayBad_eq
public import Theorems.Thm_OrderClosures_solovayC_eq
public import Theorems.Thm_OrderClosures_solovayLE_eq_sInf
public import Theorems.Thm_OrderClosures_solovayA_eq

set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u
variable (Gamma : Type u) [LinearOrder Gamma] [TopologicalSpace Gamma]
  [DiscreteTopology Gamma]
namespace OrderClosures
theorem _root_.solution [WellFoundedLT Gamma]
    (L : BooleanSubalgebra (RegularOpen (SolovayProduct Gamma)))
    (hcomplete : IsCompleteBooleanSubalgebra L)
    (hB : ∀ m n, solovayB Gamma m n ∈ L) :
    ∀ eta n, solovayA Gamma n eta ∈ L := by
  intro eta
  induction eta using WellFoundedLT.induction with
  | ind eta ih =>
      intro n
      have hLT : ∀ k, solovayLT Gamma k eta ∈ L := by
        intro k
        rw [solovayLT_eq_sSup]
        apply hcomplete
        rintro U ⟨theta, htheta, rfl⟩
        exact ih theta htheta k
      have hC : ∀ m, solovayC Gamma m n eta ∈ L := by
        intro m
        rw [solovayC_eq, solovayBad_eq, solovayStrict_eq,
          solovayNotLT_eq]
        exact L.compl_mem (L.inf_mem (L.compl_mem (hB n m))
          (L.compl_mem (hLT m)))
      have hLE : solovayLE Gamma n eta ∈ L := by
        rw [solovayLE_eq_sInf]
        apply hcomplete.sInf_mem
        rintro U ⟨m, rfl⟩
        exact hC m
      rw [solovayA_eq]
      exact L.inf_mem hLE (L.compl_mem (hLT n))
end OrderClosures
