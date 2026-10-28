-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P31.capacityEntropyUpperBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:13:54.074446+00:00
-- url     : https://prove2.me/submissions/a9fe84a8-0470-492d-84cb-063b8396524f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder

namespace X6CB

open QAlgorithms Real
open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo average)

variable {J : Type} [Fintype J] [DecidableEq J]

lemma trace_cfc {X : Matrix J J ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace = ∑ i, ((f (hX.eigenvalues i) : ℝ) : ℂ) := by
  have hU := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have : cfc f X = (hX.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((f (hX.eigenvalues i) : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix J J ℂ) := by
    rw [hX.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  rw [this, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

lemma ent_eig {ρ : Matrix J J ℂ} (hρ : ρ.IsHermitian) :
    entropy ρ = ∑ i, negMulLog (hρ.eigenvalues i) := by
  unfold entropy
  rw [trace_cfc hρ, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [negMulLog]

lemma eig_sum {ρ : Matrix J J ℂ} (hρ : IsDensityMatrix ρ) :
    ∑ i, hρ.1.1.eigenvalues i = 1 := by
  have h := hρ.1.1.trace_eq_sum_eigenvalues
  have h2 : ρ.trace = 1 := hρ.2
  have h3 : (∑ i, ((hρ.1.1.eigenvalues i : ℝ) : ℂ)) = 1 := h.symm.trans h2
  exact_mod_cast h3

lemma ent_nonneg {ρ : Matrix J J ℂ} (hρ : IsDensityMatrix ρ) : 0 ≤ entropy ρ := by
  rw [ent_eig hρ.1.1]
  refine Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (hρ.1.eigenvalues_nonneg i) ?_
  rw [← eig_sum hρ]
  exact Finset.single_le_sum (fun j _ => hρ.1.eigenvalues_nonneg j) (Finset.mem_univ i)

lemma ent_le_log [Nonempty J] {ρ : Matrix J J ℂ} (hρ : IsDensityMatrix ρ) :
    entropy ρ ≤ Real.log (Fintype.card J) := by
  have hH := hρ.1.1
  rw [ent_eig hH]
  set n : ℝ := (Fintype.card J : ℝ)
  have hn : 0 < n := by simp [n, Fintype.card_pos]
  have hs := eig_sum hρ
  have key : ∀ i, negMulLog (hH.eigenvalues i) - hH.eigenvalues i * Real.log n ≤
      n⁻¹ - hH.eigenvalues i := by
    intro i
    set t := hH.eigenvalues i
    have ht : 0 ≤ t := hρ.1.eigenvalues_nonneg i
    rcases ht.eq_or_lt with h | h
    · rw [← h]; simp [hn.le]
    · have hl := Real.one_sub_inv_le_log_of_pos (mul_pos hn h)
      rw [Real.negMulLog, Real.log_mul hn.ne' h.ne'] at *
      have : t * (1 - (n * t)⁻¹) = t - n⁻¹ := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hl h.le]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  have : (Fintype.card J : ℝ) * n⁻¹ = 1 := by simp [n, hn.ne']
  linarith

lemma chan_dens {Phi : Superop J J} (hPhi : IsChannel Phi) {ρ : Matrix J J ℂ}
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (Phi ρ) := by
  obtain ⟨m, E, hE, hP⟩ := hPhi
  rw [hP]
  refine ⟨Matrix.posSemidef_sum _ fun k _ => hρ.1.mul_mul_conjTranspose_same (E k), ?_⟩
  show Matrix.trace (∑ k, E k * ρ * (E k)ᴴ) = 1
  rw [Matrix.trace_sum]
  have : ∀ k, Matrix.trace (E k * ρ * (E k)ᴴ) = Matrix.trace ((E k)ᴴ * E k * ρ) := by
    intro k; rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [this, ← Matrix.trace_sum, ← Matrix.sum_mul]
  rw [show ∑ k, (E k)ᴴ * E k = 1 from hE, Matrix.one_mul, hρ.2]

end X6CB

open QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P31
open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo average)
open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity holevoScore)

theorem solution {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (Phi : Superop I I) (hPhi : IsChannel Phi) :
    holevoQuantity Phi ≤ Real.log (Fintype.card I : ℝ) - nuH Phi := by
  have hbdd : BddBelow (Set.range fun X : {X : Matrix I I ℂ // IsDensityMatrix X} =>
      entropy (Phi X.val)) :=
    ⟨0, by rintro _ ⟨X, rfl⟩; exact X6CB.ent_nonneg (X6CB.chan_dens hPhi X.2)⟩
  obtain ⟨i0⟩ := (inferInstance : Nonempty I)
  let e0 : QAlgorithms.Papers.Independent.Information100.P08.Ensemble I :=
    { size := 1, prob := fun _ => 1, state := fun _ => Matrix.single i0 i0 1,
      nonneg := fun _ => zero_le_one, total := by simp,
      density := fun _ => by
        refine ⟨?_, by simp⟩
        have : (Matrix.single i0 i0 (1 : ℂ)) = Matrix.vecMulVec (Pi.single i0 1)
            (star (Pi.single i0 1)) := by
          ext a b; simp [Matrix.vecMulVec_apply, Matrix.single_apply, Pi.single_apply]
          by_cases ha : a = i0 <;> by_cases hb : b = i0 <;> simp [ha, hb] <;> aesop
        rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _ }
  refine csSup_le ⟨_, e0, rfl⟩ ?_
  rintro s ⟨e, rfl⟩
  unfold holevoScore holevo
  have hd : ∀ x, IsDensityMatrix (Phi (e.state x)) := fun x => X6CB.chan_dens hPhi (e.density x)
  have hav : IsDensityMatrix (average (fun x => Phi (e.state x)) e.prob) := by
    refine ⟨Matrix.posSemidef_sum _ fun x _ => ?_, ?_⟩
    · exact (hd x).1.smul (show (0 : ℂ) ≤ (e.prob x : ℂ) from by exact_mod_cast e.nonneg x)
    · simp only [average, Matrix.trace_sum, Matrix.trace_smul, (hd _).2, smul_eq_mul, mul_one]
      exact_mod_cast e.total
  have h1 := X6CB.ent_le_log hav
  have h2 : nuH Phi ≤ ∑ x, e.prob x * entropy (Phi (e.state x)) := by
    calc nuH Phi = ∑ x, e.prob x * nuH Phi := by rw [← Finset.sum_mul, e.total, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (csInf_le hbdd ⟨⟨e.state x, e.density x⟩, rfl⟩) (e.nonneg x)
  linarith
