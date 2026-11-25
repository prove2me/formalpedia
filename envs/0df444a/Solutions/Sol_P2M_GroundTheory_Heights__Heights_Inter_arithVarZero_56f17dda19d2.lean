-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_arithVarZero_56f17dda19d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:25.202996+00:00
-- url     : https://prove2.me/submissions/a52b677a-2c7a-429f-9442-f55dcc68d0d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_killBlocks_X_891fa96bfde9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_le_comap_killBlocks_2335735e93b1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_comap_killBlocks_mono_1bda279cef92

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution : ReciprocityTheory.ChartRestriction.G.AI.I2.ArithVarZeroStatement := by
  intro K _ ι _ P hP
  obtain ⟨_, ⟨hPp, hPh, hPr⟩, hhor, hdim⟩ := hP
  have := hPp
  set m := Fintype.card K with hm
  let e : K ≃ Fin m := Fintype.equivFin K
  let S : ℕ → Set K := fun n => {k | (e k : ℕ) < n}
  let Q : ℕ → Ideal (MRing ι) := fun n => P.comap (killBlocks (S n))
  let Q2 : Ideal (MRing ι) :=
    RingHom.ker ((Int.castRingHom (ZMod 2)).comp (constantCoeff : MRing ι →+* ℤ))
  have hQp : ∀ n, (Q n).IsPrime := fun n => Ideal.IsPrime.comap _
  have hQ2p : Q2.IsPrime := RingHom.ker_isPrime _
  have hstep : ∀ n, n < m → Q n < Q (n + 1) := by
    intro n hn
    obtain ⟨i, hi⟩ := hPr (e.symm ⟨n, hn⟩)
    refine SetLike.lt_iff_le_and_exists.mpr
      ⟨comap_killBlocks_mono hPh fun k hk => Nat.lt_succ_of_lt hk, X ⟨e.symm ⟨n, hn⟩, i⟩, ?_, ?_⟩
    · show killBlocks _ _ ∈ P
      rw [killBlocks_X, if_pos (by simp [S])]
      exact P.zero_mem
    · intro h2
      change killBlocks _ _ ∈ P at h2
      rw [killBlocks_X, if_neg (by simp [S])] at h2
      exact hi h2
  have hall : ∀ f : MRing ι, killBlocks (S m) f = C (constantCoeff f) := by
    intro f
    have : killBlocks (S m) = aeval (0 : (Σ k, ι k) → MRing ι) := by
      refine MvPolynomial.algHom_ext fun p => ?_
      rw [killBlocks_X, if_pos (by simp [S]), aeval_X]
      rfl
    rw [this, aeval_zero, algebraMap_eq]
  have hQm : ∀ f, f ∈ Q m ↔ constantCoeff f = 0 := by
    intro f
    change killBlocks (S m) f ∈ P ↔ _
    rw [hall]
    change constantCoeff f ∈ P.comap (C : ℤ →+* MRing ι) ↔ _
    rw [hhor, Ideal.mem_bot]
  have hstep2 : Q m < Q2 := by
    refine SetLike.lt_iff_le_and_exists.mpr ⟨fun f hf => ?_, C 2, ?_, fun h2 => ?_⟩
    · rw [RingHom.mem_ker, RingHom.comp_apply, (hQm f).mp hf, map_zero]
    · rw [RingHom.mem_ker, RingHom.comp_apply, constantCoeff_C]
      rfl
    · have := (hQm _).mp h2
      rw [constantCoeff_C] at this
      norm_num at this
  let T : ℕ → Ideal (MRing ι) := fun n => if n ≤ m then Q n else Q2
  have hTp : ∀ n, (T n).IsPrime := by
    intro n
    dsimp only [T]
    split_ifs
    exacts [hQp n, hQ2p]
  have hPT : ∀ n, P ≤ T n := by
    intro n
    dsimp only [T]
    split_ifs
    · exact le_comap_killBlocks hPh _
    · exact (le_comap_killBlocks hPh _).trans hstep2.le
  have hTlt : ∀ n, n ≤ m → T n < T (n + 1) := by
    intro n hn
    dsimp only [T]
    rw [if_pos hn]
    rcases hn.lt_or_eq with h | h
    · rw [if_pos (Nat.succ_le_of_lt h)]
      exact hstep n h
    · rw [if_neg (by omega), h]
      exact hstep2
  let g : Fin (m + 2) → PrimeSpectrum.zeroLocus (R := MRing ι) (P : Set (MRing ι)) :=
    fun j => ⟨⟨T j, hTp j⟩, hPT j⟩
  have hg : StrictMono g := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    exact hTlt i (Nat.lt_succ_iff.mp i.isLt)
  have hlen := Order.LTSeries.length_le_krullDim (LTSeries.mk (m + 1) g hg)
  rw [← ringKrullDim_quotient, hdim] at hlen
  have h3 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 + m : ℕ) : WithBot ℕ∞) := hlen
  have h4 : m + 1 ≤ 0 + m := by exact_mod_cast h3
  omega
end GroundTheory.Heights₂.Heights.Inter
