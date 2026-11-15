-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.verifiedMassIntervals
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:45:50.237358+00:00
-- url     : https://prove2.me/submissions/660d85a6-2f05-4092-920d-95c0afaef331

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells000To020
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells021To039
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells040To053
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells054To059
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells060To070
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells071To081
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells082To091
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells092To093
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells094To103
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells104To111
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells112To118
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells119To121
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells122To128
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells129To135
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells136To142
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells143To150
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells151To158
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells159To166
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells167To173
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells174To178
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells179To181
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells182To186
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells187To190
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells191To194
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells195To197
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells198To199
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells200To201
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells202To204
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells205To206
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells207To207
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells208To210
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_coveredCells211To211
open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.Lemma9Reduction
private theorem slabAppend {u v : List (Knot × Knot)} (hu : ∀ c ∈ u, CellCovered c.1 c.2) (hv : ∀ c ∈ v, CellCovered c.1 c.2) : ∀ c ∈ u ++ v, CellCovered c.1 c.2 := List.forall_mem_append.mpr ⟨hu,hv⟩
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution : ∀ cd ∈ adjacentCells, CellCovered cd.1 cd.2 := by
  have eqs : adjacentCells = ((adjacentCells.drop 0).take 21) ++ (((adjacentCells.drop 21).take 19) ++ (((adjacentCells.drop 40).take 14) ++ (((adjacentCells.drop 54).take 6) ++ (((adjacentCells.drop 60).take 11) ++ (((adjacentCells.drop 71).take 11) ++ (((adjacentCells.drop 82).take 10) ++ (((adjacentCells.drop 92).take 2) ++ (((adjacentCells.drop 94).take 10) ++ (((adjacentCells.drop 104).take 8) ++ (((adjacentCells.drop 112).take 7) ++ (((adjacentCells.drop 119).take 3) ++ (((adjacentCells.drop 122).take 7) ++ (((adjacentCells.drop 129).take 7) ++ (((adjacentCells.drop 136).take 7) ++ (((adjacentCells.drop 143).take 8) ++ (((adjacentCells.drop 151).take 8) ++ (((adjacentCells.drop 159).take 8) ++ (((adjacentCells.drop 167).take 7) ++ (((adjacentCells.drop 174).take 5) ++ (((adjacentCells.drop 179).take 3) ++ (((adjacentCells.drop 182).take 5) ++ (((adjacentCells.drop 187).take 4) ++ (((adjacentCells.drop 191).take 4) ++ (((adjacentCells.drop 195).take 3) ++ (((adjacentCells.drop 198).take 2) ++ (((adjacentCells.drop 200).take 2) ++ (((adjacentCells.drop 202).take 3) ++ (((adjacentCells.drop 205).take 2) ++ (((adjacentCells.drop 207).take 1) ++ (((adjacentCells.drop 208).take 3) ++ (((adjacentCells.drop 211).take 1)))))))))))))))))))))))))))))))) := by decide +kernel
  rw [eqs]
  refine slabAppend coveredCells000To020 ?_
  refine slabAppend coveredCells021To039 ?_
  refine slabAppend coveredCells040To053 ?_
  refine slabAppend coveredCells054To059 ?_
  refine slabAppend coveredCells060To070 ?_
  refine slabAppend coveredCells071To081 ?_
  refine slabAppend coveredCells082To091 ?_
  refine slabAppend coveredCells092To093 ?_
  refine slabAppend coveredCells094To103 ?_
  refine slabAppend coveredCells104To111 ?_
  refine slabAppend coveredCells112To118 ?_
  refine slabAppend coveredCells119To121 ?_
  refine slabAppend coveredCells122To128 ?_
  refine slabAppend coveredCells129To135 ?_
  refine slabAppend coveredCells136To142 ?_
  refine slabAppend coveredCells143To150 ?_
  refine slabAppend coveredCells151To158 ?_
  refine slabAppend coveredCells159To166 ?_
  refine slabAppend coveredCells167To173 ?_
  refine slabAppend coveredCells174To178 ?_
  refine slabAppend coveredCells179To181 ?_
  refine slabAppend coveredCells182To186 ?_
  refine slabAppend coveredCells187To190 ?_
  refine slabAppend coveredCells191To194 ?_
  refine slabAppend coveredCells195To197 ?_
  refine slabAppend coveredCells198To199 ?_
  refine slabAppend coveredCells200To201 ?_
  refine slabAppend coveredCells202To204 ?_
  refine slabAppend coveredCells205To206 ?_
  refine slabAppend coveredCells207To207 ?_
  refine slabAppend coveredCells208To210 ?_
  exact coveredCells211To211
