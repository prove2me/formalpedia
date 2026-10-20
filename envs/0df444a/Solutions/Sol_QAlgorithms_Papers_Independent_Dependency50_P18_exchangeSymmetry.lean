-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.exchangeSymmetry
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:49:57.731987+00:00
-- url     : https://prove2.me/submissions/a604f886-87fa-43da-9313-7fcbb98d14f0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]

lemma g52a_swap_psd {A B : Type} [Fintype A] [Fintype B] {M : Matrix (A × B) (A × B) ℂ}
    (hM : M.PosSemidef) : (swap M).PosSemidef := hM.submatrix Prod.swap

lemma g52a_swap_swap {A B : Type} (M : Matrix (A × B) (A × B) ℂ) : swap (swap M) = M := by
  ext i j; rfl

lemma g52a_feas_swap {A B : Type} [Fintype A] [Fintype B]
    (s : Matrix (A × B) (A × B) ℂ) (k : Matrix A A ℂ) (l : Matrix B B ℂ)
    (v : Matrix (A × B) (A × B) ℂ) (h : GammaFeasible s k l v) :
    GammaFeasible (swap s) l k (swap v) := by
  obtain ⟨hk, hl, hv, h1, h2, h3, h4⟩ := h
  have hgs : ∀ X : Matrix (A × B) (A × B) ℂ,
      QAlgorithms.Papers.Independent.Information100.P04.gamma (swap X) =
        (swap (QAlgorithms.Papers.Independent.Information100.P04.gamma X)).transpose := by
    intro X; ext i j; rfl
  have ha : swap v + swap s = swap (v + s) := by ext i j; rfl
  have hs : swap v - swap s = swap (v - s) := by ext i j; rfl
  have hk1 : Matrix.kronecker l k + swap v = swap (Matrix.kronecker k l + v) := by
    ext i j; simp [swap, Matrix.kronecker, mul_comm]
  have hk2 : Matrix.kronecker l k - swap v = swap (Matrix.kronecker k l - v) := by
    ext i j; simp [swap, Matrix.kronecker, mul_comm]
  refine ⟨hl, hk, hv.submatrix Prod.swap, ?_, ?_, ?_, ?_⟩
  · rw [ha, hgs]; exact (g52a_swap_psd h1).transpose
  · rw [hs, hgs]; exact (g52a_swap_psd h2).transpose
  · rw [hk1]; exact g52a_swap_psd h3
  · rw [hk2]; exact g52a_swap_psd h4

lemma g52a_trace_kron {A B : Type} [Fintype A] [Fintype B] (k : Matrix A A ℂ) (l : Matrix B B ℂ) :
    (Matrix.kronecker k l).trace = k.trace * l.trace := Matrix.trace_kronecker k l

lemma g52a_gauge_le {A B : Type} [Fintype A] [Fintype B] (s : Matrix (A × B) (A × B) ℂ) :
    correlationGauge (swap s) ≤ correlationGauge s := by
  apply sInf_le_sInf
  rintro r ⟨k, l, v, hf, rfl⟩
  refine ⟨l, k, swap v, g52a_feas_swap s k l v hf, ?_⟩
  rw [g52a_trace_kron, g52a_trace_kron, mul_comm]

lemma g52a_gauge_swap {A B : Type} [Fintype A] [Fintype B] (s : Matrix (A × B) (A × B) ℂ) :
    correlationGauge (swap s) = correlationGauge s := by
  refine le_antisymm (g52a_gauge_le s) ?_
  have := g52a_gauge_le (swap s)
  rwa [g52a_swap_swap] at this

lemma g52a_swap_channel {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    QAlgorithms.IsChannel (fun X : Matrix (A × B) (A × B) ℂ => swap X) := by
  let P : Matrix (B × A) (A × B) ℂ := Matrix.of fun x y => if y = x.swap then 1 else 0
  have hPM : ∀ (M : Matrix (A × B) (A × B) ℂ) (x : B × A) r, (P * M) x r = M x.swap r := by
    intro M x r
    rw [Matrix.mul_apply, Finset.sum_eq_single x.swap]
    · simp [P]
    · intro t _ ht; simp [P, ht]
    · simp
  have hMP : ∀ (Y : Matrix (B × A) (A × B) ℂ) x (y : B × A), (Y * Matrix.conjTranspose P) x y = Y x y.swap := by
    intro Y x y
    rw [Matrix.mul_apply, Finset.sum_eq_single y.swap]
    · simp [P]
    · intro t _ ht; simp [P, ht]
    · simp
  refine ⟨1, fun _ => P, ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    simp only [Finset.univ_unique, Finset.sum_singleton]
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single a.swap]
    · by_cases hab : a = b
      · subst hab; simp [P]
      · have : b ≠ a := Ne.symm hab
        have h2 : ¬ (b = a.swap.swap) := by simpa using this
        simp [P, Matrix.one_apply, hab, h2, this]
    · intro t _ ht
      have : ¬ (a = t.swap) := by
        rintro rfl; exact ht (by simp)
      simp [P, this]
    · simp
  · intro rho
    unfold QAlgorithms.krausApply
    simp only [Finset.univ_unique, Finset.sum_singleton]
    ext x y
    rw [hMP, hPM]
    rfl

lemma g52a_swap_density {A B : Type} [Fintype A] [Fintype B] {rho : Matrix (A × B) (A × B) ℂ}
    (h : QAlgorithms.IsDensityMatrix rho) : QAlgorithms.IsDensityMatrix (swap rho) := by
  refine ⟨g52a_swap_psd h.1, ?_⟩
  rw [← h.2]
  exact Fintype.sum_equiv (Equiv.prodComm B A) _ _ (fun _ => rfl)

lemma g52a_cap_le {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (D : Divergence) (hD : IsGeneralizedDivergence D)
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    capitalGamma D (swap rho) ≤ capitalGamma D rho := by
  unfold capitalGamma
  apply le_sInf
  rintro r ⟨sigma, hs, hg, rfl⟩
  refine (sInf_le (show D (swap rho) (swap sigma) ∈ {r | ∃ τ : Matrix (B × A) (B × A) ℂ,
    τ.PosSemidef ∧ correlationGauge τ ≤ 1 ∧ r = D (swap rho) τ} from
    ⟨swap sigma, g52a_swap_psd hs, by rwa [g52a_gauge_swap], rfl⟩)).trans ?_
  exact hD.dataProcessing rho sigma (fun X => swap X) hrho hs g52a_swap_channel

/-- Proposition 1, PDF p.2, (6)–(7): actual subsystem exchange, including zero PSD input. -/
theorem solution (D : Divergence) (hD : IsGeneralizedDivergence D) :
    (∀ sigma : Matrix (A × B) (A × B) ℂ, sigma.PosSemidef →
      cGamma sigma = cGamma (swap sigma)) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D rho = capitalGamma D (swap rho)) := by
  refine ⟨fun sigma _ => ?_, fun rho hrho => ?_⟩
  · unfold cGamma; rw [g52a_gauge_swap]
  · refine le_antisymm ?_ (g52a_cap_le D hD rho hrho)
    have := g52a_cap_le D hD (swap rho) (g52a_swap_density hrho)
    rwa [g52a_swap_swap] at this


end

