-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_linear_D5_0004
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:37.436732+00:00
-- url     : https://prove2.me/submissions/ed76cf1c-3711-41b6-95da-dd0cb78ef1b8

import Definitions.Def_RealPinwheel_FiveSixths_LinearTreeD5_0004
import Theorems.Thm_RealPinwheel_FiveSixths_checked_linear_D5_0000
import Theorems.Thm_RealPinwheel_FiveSixths_checked_linear_D5_0001
import Theorems.Thm_RealPinwheel_FiveSixths_checked_linear_D5_0002
import Theorems.Thm_RealPinwheel_FiveSixths_checked_linear_D5_0003
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : linearCoverCheck 216 codeFunctionD5 linearContextD5_0004 linearTreeD5_0004 = true := by
  unfold linearTreeD5_0004
  rw [linearCoverCheck]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  ·
    rw [linearCoverCheck]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨by decide, ?_⟩, ?_⟩
    ·
      decide +kernel
    ·
      rw [linearCoverCheck]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨by decide, ?_⟩, ?_⟩
      ·
        decide +kernel
      ·
        rw [linearCoverCheck]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨by decide, ?_⟩, ?_⟩
        ·
          decide +kernel
        ·
          decide +kernel
  ·
    rw [linearCoverCheck]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨by decide, ?_⟩, ?_⟩
    ·
      rw [linearCoverCheck]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨by decide, ?_⟩, ?_⟩
      ·
        exact RealPinwheel.FiveSixths.checked_linear_D5_0000
      ·
        exact RealPinwheel.FiveSixths.checked_linear_D5_0001
    ·
      rw [linearCoverCheck]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨by decide, ?_⟩, ?_⟩
      ·
        rw [linearCoverCheck]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨by decide, ?_⟩, ?_⟩
        ·
          decide +kernel
        ·
          rw [linearCoverCheck]
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨by decide, ?_⟩, ?_⟩
          ·
            exact RealPinwheel.FiveSixths.checked_linear_D5_0002
          ·
            exact RealPinwheel.FiveSixths.checked_linear_D5_0003
      ·
        rw [linearCoverCheck]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨by decide, ?_⟩, ?_⟩
        ·
          rw [linearCoverCheck]
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨by decide, ?_⟩, ?_⟩
          ·
            rw [linearCoverCheck]
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨⟨by decide, ?_⟩, ?_⟩
            ·
              decide +kernel
            ·
              rw [linearCoverCheck]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              refine ⟨⟨by decide, ?_⟩, ?_⟩
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    decide +kernel
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          decide +kernel
                        ·
                          rw [linearCoverCheck]
                          simp only [Bool.and_eq_true, decide_eq_true_eq]
                          refine ⟨⟨by decide, ?_⟩, ?_⟩
                          ·
                            decide +kernel
                          ·
                            rw [linearCoverCheck]
                            simp only [Bool.and_eq_true, decide_eq_true_eq]
                            refine ⟨⟨by decide, ?_⟩, ?_⟩
                            ·
                              decide +kernel
                            ·
                              decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          decide +kernel
                        ·
                          rw [linearCoverCheck]
                          simp only [Bool.and_eq_true, decide_eq_true_eq]
                          refine ⟨⟨by decide, ?_⟩, ?_⟩
                          ·
                            decide +kernel
                          ·
                            decide +kernel
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          decide +kernel
                        ·
                          decide +kernel
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          decide +kernel
                        ·
                          decide +kernel
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          decide +kernel
                        ·
                          decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          rw [linearCoverCheck]
                          simp only [Bool.and_eq_true, decide_eq_true_eq]
                          refine ⟨⟨by decide, ?_⟩, ?_⟩
                          ·
                            decide +kernel
                          ·
                            decide +kernel
                        ·
                          decide +kernel
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          decide +kernel
                        ·
                          decide +kernel
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        decide +kernel
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    decide +kernel
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        decide +kernel
          ·
            rw [linearCoverCheck]
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨⟨by decide, ?_⟩, ?_⟩
            ·
              rw [linearCoverCheck]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              refine ⟨⟨by decide, ?_⟩, ?_⟩
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    decide +kernel
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          decide +kernel
                        ·
                          rw [linearCoverCheck]
                          simp only [Bool.and_eq_true, decide_eq_true_eq]
                          refine ⟨⟨by decide, ?_⟩, ?_⟩
                          ·
                            decide +kernel
                          ·
                            decide +kernel
                      ·
                        decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          rw [linearCoverCheck]
                          simp only [Bool.and_eq_true, decide_eq_true_eq]
                          refine ⟨⟨by decide, ?_⟩, ?_⟩
                          ·
                            decide +kernel
                          ·
                            decide +kernel
                        ·
                          decide +kernel
                      ·
                        decide +kernel
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          decide +kernel
                        ·
                          decide +kernel
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          decide +kernel
                        ·
                          decide +kernel
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        decide +kernel
                    ·
                      decide +kernel
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          rw [linearCoverCheck]
                          simp only [Bool.and_eq_true, decide_eq_true_eq]
                          refine ⟨⟨by decide, ?_⟩, ?_⟩
                          ·
                            decide +kernel
                          ·
                            decide +kernel
                        ·
                          decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        decide +kernel
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        decide +kernel
                    ·
                      decide +kernel
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      decide +kernel
                    ·
                      decide +kernel
                  ·
                    decide +kernel
            ·
              rw [linearCoverCheck]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              refine ⟨⟨by decide, ?_⟩, ?_⟩
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        rw [linearCoverCheck]
                        simp only [Bool.and_eq_true, decide_eq_true_eq]
                        refine ⟨⟨by decide, ?_⟩, ?_⟩
                        ·
                          decide +kernel
                        ·
                          rw [linearCoverCheck]
                          simp only [Bool.and_eq_true, decide_eq_true_eq]
                          refine ⟨⟨by decide, ?_⟩, ?_⟩
                          ·
                            decide +kernel
                          ·
                            decide +kernel
                      ·
                        decide +kernel
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        decide +kernel
                    ·
                      decide +kernel
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    decide +kernel
                  ·
                    decide +kernel
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  decide +kernel
                ·
                  decide +kernel
        ·
          rw [linearCoverCheck]
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨by decide, ?_⟩, ?_⟩
          ·
            rw [linearCoverCheck]
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨⟨by decide, ?_⟩, ?_⟩
            ·
              rw [linearCoverCheck]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              refine ⟨⟨by decide, ?_⟩, ?_⟩
              ·
                decide +kernel
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    decide +kernel
                  ·
                    decide +kernel
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      decide +kernel
                    ·
                      decide +kernel
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      decide +kernel
                    ·
                      decide +kernel
            ·
              rw [linearCoverCheck]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              refine ⟨⟨by decide, ?_⟩, ?_⟩
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      decide +kernel
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        decide +kernel
                  ·
                    rw [linearCoverCheck]
                    simp only [Bool.and_eq_true, decide_eq_true_eq]
                    refine ⟨⟨by decide, ?_⟩, ?_⟩
                    ·
                      rw [linearCoverCheck]
                      simp only [Bool.and_eq_true, decide_eq_true_eq]
                      refine ⟨⟨by decide, ?_⟩, ?_⟩
                      ·
                        decide +kernel
                      ·
                        decide +kernel
                    ·
                      decide +kernel
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    decide +kernel
                  ·
                    decide +kernel
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  decide +kernel
                ·
                  decide +kernel
          ·
            rw [linearCoverCheck]
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨⟨by decide, ?_⟩, ?_⟩
            ·
              rw [linearCoverCheck]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              refine ⟨⟨by decide, ?_⟩, ?_⟩
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  decide +kernel
                ·
                  decide +kernel
            ·
              rw [linearCoverCheck]
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              refine ⟨⟨by decide, ?_⟩, ?_⟩
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    decide +kernel
                  ·
                    decide +kernel
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    decide +kernel
                  ·
                    decide +kernel
              ·
                rw [linearCoverCheck]
                simp only [Bool.and_eq_true, decide_eq_true_eq]
                refine ⟨⟨by decide, ?_⟩, ?_⟩
                ·
                  rw [linearCoverCheck]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  refine ⟨⟨by decide, ?_⟩, ?_⟩
                  ·
                    decide +kernel
                  ·
                    decide +kernel
                ·
                  decide +kernel
