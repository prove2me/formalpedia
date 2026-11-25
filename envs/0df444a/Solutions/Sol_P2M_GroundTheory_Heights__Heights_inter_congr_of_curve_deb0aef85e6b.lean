-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_inter_congr_of_curve_deb0aef85e6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:05:19.744679+00:00
-- url     : https://prove2.me/submissions/c78c2730-974b-4413-b760-d082ba23deac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_recR_congr_da8aa240434b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ)
    (hII : Geo.IsIntersectionFamily II) {W : Ideal (MvPolynomial (Coord n) ℤ)}
    (hW : Geo.IsArithVar (ι := blockIdx n) W 1) {B B' : Geo.HermLine (blockIdx n)}
    (hB : Geo.IsSmoothHerm B) (hB' : Geo.IsSmoothHerm B') (ha : B.a = B'.a)
    (hh : ∀ z ∈ Geo.mcPts W, B.h z = B'.h z) : II W 1 ![B] = II W 1 ![B'] := by
  obtain ⟨-, hAdd, hR⟩ := hII
  have hW' : Geo.IsArithVar (ι := blockIdx n) W (0 + 1) := hW
  have hprime : W.IsPrime := hW.2.1.1
  have hrel : ∀ k, ∃ i, (X ⟨k, i⟩ : MvPolynomial (Coord n) ℤ) ∉ W := hW.2.1.2.2
  let c : (k : ι) → Fin (n k + 1) := fun k ↦ (hrel k).choose
  have hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ W := fun k ↦ (hrel k).choose_spec
  have hmon : ∀ d : ι → ℕ, chartMonomial c d ∉ W := by
    intro d h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hc k (hprime.mem_of_pow_mem _ hk)
  have hsnoc : ∀ C : Geo.HermLine (blockIdx n),
      (Fin.snoc (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) C : Fin 1 → _) = ![C] := by
    intro C
    funext i
    fin_cases i
    rfl
  have hL : ∀ j : Fin 0, Geo.IsSmoothHerm ((Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) j) :=
    fun j ↦ j.elim0
  have key : ∀ (C C' : Geo.HermLine (blockIdx n)) (d : ι → ℕ), Geo.IsSmoothHerm C →
      Geo.IsSmoothHerm C' → (∀ k, C.a k = d k) → (∀ k, C'.a k = d k) →
      (∀ z ∈ Geo.mcPts W, C.h z = C'.h z) → II W 1 ![C] = II W 1 ![C'] := by
    intro C C' d hC hC' hd hd' hCC
    have hs := (geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d)
    have h1 := hR W 0 Fin.elim0 C (chartMonomial c d) d hW' hL hC hd hs (hmon d)
    have h2 := hR W 0 Fin.elim0 C' (chartMonomial c d) d hW' hL hC' hd' hs (hmon d)
    rw [hsnoc] at h1 h2
    rw [h1, h2, recR_congr II W Fin.elim0 (chartMonomial c d) hCC]
  let m : ι → ℕ := fun k ↦ (B.a k).natAbs
  let S : Geo.HermLine (blockIdx n) := (HermLine.standardPow (n := n) m).toGeo
  have hS : Geo.IsSmoothHerm S := HermLine.isSmoothHerm_toGeo _
  have hSa : ∀ k, S.a k = m k := fun k ↦ rfl
  have hBS : Geo.IsSmoothHerm (B.tensor S) := ContDiffOn.mul hB hS
  have hBS' : Geo.IsSmoothHerm (B'.tensor S) := ContDiffOn.mul hB' hS
  have hsum := key (B.tensor S) (B'.tensor S) (fun k ↦ (B.a k + m k).toNat) hBS hBS'
    (fun k ↦ by
      show B.a k + S.a k = _
      rw [hSa]
      simp only [m]
      omega)
    (fun k ↦ by
      show B'.a k + S.a k = _
      rw [hSa, ← ha]
      simp only [m]
      omega)
    (fun z hz ↦ by
      show B.h z * S.h z = B'.h z * S.h z
      rw [hh z hz])
  have hadd := hAdd W 0 Fin.elim0 B S hW' hL hB hS
  have hadd' := hAdd W 0 Fin.elim0 B' S hW' hL hB' hS
  rw [hsnoc, hsnoc, hsnoc] at hadd hadd'
  linarith
end GroundTheory.Heights₂.Heights
