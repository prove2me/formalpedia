-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P01.path_instrument
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:44:20.991882+00:00
-- url     : https://prove2.me/submissions/0f33bee4-8b7f-43ab-bed6-80763e6a7bae

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P01
noncomputable section

open scoped Matrix

open QAlgorithms.Papers.Independent.Claimed50.P01
attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50
open scoped ComplexOrder

theorem g58c_seq_succ {d n : ℕ} (C : CGSystem d) (p : QAlgorithms.Papers.Independent.Claimed50.P01.Path d (n + 1)) :
    sequentialKraus C (n + 1) p.val = C.block (terminal (pathPrefix p).val) (terminal p.val) *
      (Matrix.kronecker (sequentialKraus C n (pathPrefix p).val)
        (1 : Matrix (Fin d) (Fin d) ℂ)).submatrix id
          (fun w : Fin (n + 1) → Fin d => (Fin.init w, w (Fin.last n))) := rfl

theorem g58c_seq_schur {d : ℕ} (C : CGSystem d) :
    ∀ (n : ℕ) (p : QAlgorithms.Papers.Independent.Claimed50.P01.Path d n), sequentialKraus C n p.val = schurBlock C p := by
  intro n
  induction n with
  | zero => intro p; ext q w; rfl
  | succ n ih =>
    intro p
    rw [g58c_seq_succ, ih (pathPrefix p)]
    ext q w
    simp only [schurBlock, gtTransform, Matrix.submatrix_apply, Matrix.mul_apply, id,
      Fintype.sum_prod_type, Fintype.sum_sigma, superCG, Matrix.of_apply, Matrix.kronecker_apply]
    rw [Finset.sum_eq_single (pathPrefix p)]
    · simp only [dif_pos rfl]
      rfl
    · intro p' _ hp'
      refine Finset.sum_eq_zero (fun q' _ => Finset.sum_eq_zero (fun j _ => ?_))
      rw [dif_neg (Ne.symm hp')]; simp
    · simp

theorem g58c_pad_app {d k : ℕ} (C : CGSystem d) (p : QAlgorithms.Papers.Independent.Claimed50.P01.Path d k) (r : ℕ)
    (a : QIndex (terminal p.val)) (u : Fin r → Fin d) (x : Fin k → Fin d) (u' : Fin r → Fin d) :
    paddedKraus C p r (a, u) (Fin.append x u') = if u = u' then sequentialKraus C k p.val a x else 0 := by
  simp only [paddedKraus, Matrix.of_apply, Fin.append_right, Fin.append_left]

theorem g58c_tu {d k : ℕ} (C : CGSystem d) (p : QAlgorithms.Papers.Independent.Claimed50.P01.Path d k) (r : ℕ)
    (rho : Matrix ((Fin (k + r) → Fin d)) ((Fin (k + r) → Fin d)) ℂ) :
    traceUnread (paddedBranch C p rho) =
      sequentialKraus C k p.val * prefixDensity k r rho * (sequentialKraus C k p.val)ᴴ := by
  ext a b
  simp only [traceUnread, paddedBranch, Matrix.mul_apply, Matrix.conjTranspose_apply,
    prefixDensity, Matrix.of_apply]
  simp_rw [← (Fin.appendEquiv k r).sum_comp]
  simp only [Fin.appendEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, g58c_pad_app]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, apply_ite star,
    star_zero, mul_ite, mul_zero]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]

theorem g58c_tu_psd {A B : Type} [Fintype A] [Fintype B]
    (X : Matrix (A × B) (A × B) ℂ) (hX : X.PosSemidef) : (traceUnread X).PosSemidef := by
  have : traceUnread X = ∑ u : B, X.submatrix (fun a => (a, u)) (fun a => (a, u)) := by
    ext a b; simp [traceUnread, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ (fun u _ => hX.submatrix _)

theorem g58c_tu_trace {A B : Type} [Fintype A] [Fintype B]
    (X : Matrix (A × B) (A × B) ℂ) : (traceUnread X).trace = X.trace := by
  simp [traceUnread, Matrix.trace, Fintype.sum_prod_type]

theorem g58c_trace_real {A : Type} [Fintype A] (X : Matrix A A ℂ) (hX : X.PosSemidef) :
    X.trace = ((X.trace.re : ℝ) : ℂ) := by
  have h := hX.trace_nonneg
  rw [Complex.nonneg_iff] at h
  apply Complex.ext <;> simp [← h.2]

/-- Eqs.(23),(34)-(44): equality of the sequential CP instrument with each
coherent Schur block, together with its positive-probability conditional
retained state and partial-trace readout (PDF pp.7-9). The induction uses the
previous label in the latest CG factor, correcting the type mismatch in the
printed Eqs.(42)-(44). This is the defining-register algorithm of this paper;
no dual-register or mixed-Schur extension is asserted. -/
theorem solution {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (C : CGSystem d) (p : QAlgorithms.Papers.Independent.Claimed50.P01.Path d n) :
    sequentialKraus C n p.val = schurBlock C p ∧
    (∀ rho : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ,
      sequentialBranch C p rho = schurBlock C p * rho * (schurBlock C p)ᴴ) ∧
    (∀ (r : ℕ) (rho : Matrix ((Fin (n + r) → Fin d)) ((Fin (n + r) → Fin d)) ℂ),
      IsDensityMatrix rho →
      traceUnread (paddedBranch C p rho) =
        schurBlock C p * prefixDensity n r rho * (schurBlock C p)ᴴ ∧
      (pathProbability C p (prefixDensity n r rho) = 0 → paddedBranch C p rho = 0) ∧
      (0 < pathProbability C p (prefixDensity n r rho) →
        let weight : ℂ := (pathProbability C p (prefixDensity n r rho) : ℂ)⁻¹
        IsDensityMatrix (weight • paddedBranch C p rho) ∧
        IsDensityMatrix (weight • sequentialBranch C p (prefixDensity n r rho)) ∧
        traceUnread (weight • paddedBranch C p rho) =
          weight • (schurBlock C p * prefixDensity n r rho * (schurBlock C p)ᴴ))) := by
  have h1 := g58c_seq_schur C n p
  refine ⟨h1, fun rho => by simp [sequentialBranch, h1], ?_⟩
  intro r rho hrho
  have hpad : (paddedBranch C p rho).PosSemidef := hrho.1.mul_mul_conjTranspose_same _
  have htu := g58c_tu C p r rho
  have hseq : sequentialBranch C p (prefixDensity n r rho) = traceUnread (paddedBranch C p rho) := by
    rw [htu]; rfl
  have hspsd : (sequentialBranch C p (prefixDensity n r rho)).PosSemidef := by
    rw [hseq]; exact g58c_tu_psd _ hpad
  have htr : (paddedBranch C p rho).trace = (pathProbability C p (prefixDensity n r rho) : ℂ) := by
    unfold pathProbability; rw [hseq, g58c_tu_trace]; exact g58c_trace_real _ hpad
  have htr2 : (sequentialBranch C p (prefixDensity n r rho)).trace =
      (pathProbability C p (prefixDensity n r rho) : ℂ) := by
    rw [hseq, g58c_tu_trace, htr]
  refine ⟨by rw [htu, h1], ?_, ?_⟩
  · intro h0
    rw [h0] at htr
    exact (hpad.trace_eq_zero_iff).1 (by simpa using htr)
  · intro hpos
    dsimp only
    have hw : (0 : ℂ) ≤ ((pathProbability C p (prefixDensity n r rho) : ℂ))⁻¹ := by
      rw [← Complex.ofReal_inv]; exact Complex.zero_le_real.2 (inv_nonneg.2 hpos.le)
    have hne : ((pathProbability C p (prefixDensity n r rho) : ℂ)) ≠ 0 := by
      exact_mod_cast hpos.ne'
    refine ⟨⟨hpad.smul hw, ?_⟩, ⟨hspsd.smul hw, ?_⟩, ?_⟩
    · rw [Matrix.trace_smul, htr, smul_eq_mul, inv_mul_cancel₀ hne]
    · rw [Matrix.trace_smul, htr2, smul_eq_mul, inv_mul_cancel₀ hne]
    · rw [← h1, ← htu]
      ext a b
      simp [traceUnread, Finset.mul_sum]


end
