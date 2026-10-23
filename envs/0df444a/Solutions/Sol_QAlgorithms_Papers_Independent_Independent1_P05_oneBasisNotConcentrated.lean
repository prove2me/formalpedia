-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P05.oneBasisNotConcentrated
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:55:13.142988+00:00
-- url     : https://prove2.me/submissions/c3eb3213-fc39-4682-8fcc-44cc2b06bff4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_conjugateBasisUncertainty
import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_oneBasisClusterCardProductBound

noncomputable section
open scoped Matrix ComplexOrder
open QAlgorithms
open PresentedCSS
open QAlgorithms.Papers.Independent.Independent1.P05

theorem solution {n mx mz : ℕ} (C : CheckPresentation n mx mz)
    (hn : 0 < n) (hmx : 0 < mx) (hmz : 0 < mz) (hk : 1 ≤ C.logicalDimension)
    (c1 c2 delta0 eps1 : ℝ) (hcluster : NLTS.ClustersApproximateCodewords C c1 c2 delta0)
    (heps : 0 ≤ eps1) (hdomain : 2*eps1 < delta0) (hsmall : 4*c1*eps1 < c2)
    (hcutoff : 2*c1*eps1 ≤ (((C.logicalDimension : ℝ)-1)/(4*n))^2)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ B ∈ nltsClasses C c1 eps1 false, nltsMass rho false B < 99/100) ∨
    (∀ B ∈ nltsClasses C c1 eps1 true, nltsMass rho true B < 99/100) := by
  by_contra h
  push_neg at h
  rcases h with ⟨⟨Bz, hz, hmz⟩, ⟨Bx, hx, hmx'⟩⟩
  have hmassz : (99:ℝ)/100 ≤ nltsMass rho false Bz := hmz
  have hunc := conjugateBasisUncertainty rho hrho Bz Bx
  have hcards := oneBasisClusterCardProductBound C hn hk c1 eps1 hcluster.1 heps
    hcutoff Bz hz Bx hx
  have hsqrt : 2*Real.sqrt (1-nltsMass rho false Bz) ≤ 1/5 := by
    by_cases hle : nltsMass rho false Bz ≤ 1
    · have hs : Real.sqrt (1-nltsMass rho false Bz) ≤ 1/10 := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · linarith
        · nlinarith [sq_nonneg (Real.sqrt (1-nltsMass rho false Bz)),
            Real.sq_sqrt (show 0 ≤ 1-nltsMass rho false Bz by linarith)]
      linarith
    · have hzneg : 1-nltsMass rho false Bz ≤ 0 := by linarith
      rw [Real.sqrt_eq_zero_of_nonpos hzneg]
      norm_num
  have hbound : nltsMass rho true Bx ≤ 7/10 := by
    calc
      nltsMass rho true Bx ≤ 2*Real.sqrt (1-nltsMass rho false Bz) +
          (Bz.card : ℝ)*Bx.card/(2:ℝ)^n := hunc
      _ ≤ 1/5 + 1/2 := add_le_add hsqrt hcards
      _ = 7/10 := by norm_num
  linarith
