-- Prove2me | solution 1 for RobustOpt2009.Adjustable.quadratic_rules_sdp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:48:01.35227+00:00
-- url     : https://prove2.me/submissions/da8601cd-a66d-40e1-b3bb-32de08dc02e3

import Theorems.Thm_ModernConvex_SLemma_s_lemma
import Definitions.Def_RobustOpt2009_Adjustable_Model

open Matrix RobustOpt2009.Adjustable

namespace X8Q

variable {L r : ℕ}

lemma x8_qf_block (s : ℝ) (v : Fin L → ℝ) (W : Matrix (Fin L) (Fin L) ℝ)
    (y : Option (Fin L) → ℝ) :
    y ⬝ᵥ (momentBlock s v W *ᵥ y) = s * y none ^ 2 + 2 * y none * ∑ l, v l * y (some l) +
      ∑ l, ∑ h, W l h * y (some l) * y (some h) := by
  simp only [dotProduct, mulVec, Fintype.sum_option, momentBlock, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]
  have e1 : ∑ i, y (some i) * (v i * y none) = ∑ l, y none * (v l * y (some l)) :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [e1]
  have e2 : ∑ i, ∑ j, y (some i) * (W i j * y (some j)) =
      ∑ l, ∑ h, W l h * y (some l) * y (some h) :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e2]
  simp only [two_mul, add_mul, Finset.sum_add_distrib]
  ring

lemma x8_normQ (Q : Matrix (Fin r) (Fin L) ℝ) (z : Fin L → ℝ) :
    ∑ i, (Q *ᵥ z) i ^ 2 = ∑ l, ∑ h, (Q.transpose * Q) l h * z l * z h := by
  simp only [mulVec, dotProduct, mul_apply, transpose_apply, sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  refine Finset.sum_congr rfl fun i _ => by ring

lemma x8_block_herm (s : ℝ) (v : Fin L → ℝ) (W : Matrix (Fin L) (Fin L) ℝ) (hW : W.transpose = W) :
    (momentBlock s v W).IsHermitian := by
  ext p q
  cases p <;> cases q <;> simp [momentBlock, conjTranspose_apply]
  rename_i a b
  exact congrFun (congrFun hW a) b

lemma x8_form_sub {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix κ κ ℝ) (e : ι ≃ κ)
    (x : ι → ℝ) :
    x ⬝ᵥ (M.submatrix e e *ᵥ x) = (x ∘ e.symm) ⬝ᵥ (M *ᵥ (x ∘ e.symm)) := by
  simp only [dotProduct, mulVec, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.symm_apply_apply]
  congr 1
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply]

theorem x8_ell (Q : Matrix (Fin r) (Fin L) ℝ) (hQ : Function.Injective Q.mulVec) (c : ℝ)
    (v : Fin L → ℝ) (W : Matrix (Fin L) (Fin L) ℝ) (hW : W.transpose = W) :
    (∀ z ∈ ellipsoid Q, 0 ≤ c + 2 * ∑ l, v l * z l + ∑ l, ∑ h, W l h * z l * z h) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧
        (momentBlock (c - lam) v (fun l h => W l h + lam * (Q.transpose * Q) l h)).PosSemidef := by
  set G := Q.transpose * Q with hG
  have hGs : G.transpose = G := by simp [hG, transpose_mul]
  constructor
  · intro hf
    set e := finSuccEquiv L
    obtain ⟨A, hAd⟩ : ∃ A, A = momentBlock (1 : ℝ) (0 : Fin L → ℝ) (fun l h => -G l h) := ⟨_, rfl⟩
    obtain ⟨B, hBd⟩ : ∃ B, B = momentBlock c v W := ⟨_, rfl⟩
    have hA : A.IsHermitian := by
      rw [hAd]
      refine x8_block_herm _ _ _ ?_
      ext l h
      show -G h l = -G l h
      rw [show G h l = G.transpose l h from rfl, hGs]
    have hB : B.IsHermitian := by rw [hBd]; exact x8_block_herm _ _ _ hW
    have hfA : ∀ y : Option (Fin L) → ℝ, y ⬝ᵥ (A *ᵥ y) =
        y none ^ 2 - ∑ i, (Q *ᵥ (fun l => y (some l))) i ^ 2 := by
      intro y
      have h1 := x8_qf_block (1 : ℝ) (0 : Fin L → ℝ) (fun l h => -G l h) y
      rw [hAd, h1, x8_normQ]
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero, one_mul,
        neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
      rfl
    have hfB : ∀ y : Option (Fin L) → ℝ, y ⬝ᵥ (B *ᵥ y) = c * y none ^ 2 +
        2 * y none * ∑ l, v l * y (some l) + ∑ l, ∑ h, W l h * y (some l) * y (some h) :=
      fun y => by rw [hBd]; exact x8_qf_block _ _ _ y
    have key : ∀ y : Option (Fin L) → ℝ, 0 ≤ y ⬝ᵥ (A *ᵥ y) → 0 ≤ y ⬝ᵥ (B *ᵥ y) := by
      intro y hy
      rw [hfA] at hy
      rw [hfB]
      by_cases h0 : y none = 0
      · have hn : ∑ i, (Q *ᵥ (fun l => y (some l))) i ^ 2 = 0 := by
          rw [h0] at hy
          apply le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => sq_nonneg _)
        have hQz : Q *ᵥ (fun l => y (some l)) = Q *ᵥ 0 := by
          rw [mulVec_zero]
          ext i
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
            ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hn i (Finset.mem_univ _))
        have hz := hQ hQz
        have hz' : ∀ l, y (some l) = 0 := fun l => congrFun hz l
        simp [h0, hz']
      · set z : Fin L → ℝ := fun l => (y none)⁻¹ * y (some l)
        have hzQ : Q *ᵥ z = (y none)⁻¹ • (Q *ᵥ (fun l => y (some l))) := by
          rw [← mulVec_smul]; rfl
        have hzell : z ∈ ellipsoid Q := by
          show ∑ i, (Q *ᵥ z) i ^ 2 ≤ 1
          rw [hzQ]
          simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
          rw [inv_pow, inv_mul_le_one₀ (by positivity)]
          linarith
        have := hf z hzell
        simp only [z] at this
        have hpos : 0 < y none ^ 2 := by positivity
        have e1 : ∑ l, v l * ((y none)⁻¹ * y (some l)) = (y none)⁻¹ * ∑ l, v l * y (some l) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        have e2 : ∑ l, ∑ h, W l h * ((y none)⁻¹ * y (some l)) * ((y none)⁻¹ * y (some h)) =
            ((y none)⁻¹) ^ 2 * ∑ l, ∑ h, W l h * y (some l) * y (some h) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        rw [e1, e2] at this
        have := mul_nonneg hpos.le this
        have e3 : y none ^ 2 * (c + 2 * ((y none)⁻¹ * ∑ l, v l * y (some l)) +
            (y none)⁻¹ ^ 2 * ∑ l, ∑ h, W l h * y (some l) * y (some h)) =
            c * y none ^ 2 + 2 * y none * ∑ l, v l * y (some l) +
              ∑ l, ∑ h, W l h * y (some l) * y (some h) := by
          field_simp
        linarith
    have hA' : (A.submatrix e e).IsHermitian := hA.submatrix _
    have hB' : (B.submatrix e e).IsHermitian := hB.submatrix _
    have hfeas : ∃ x : Fin (L + 1) → ℝ, 0 < x ⬝ᵥ (A.submatrix e e *ᵥ x) := by
      refine ⟨(fun o : Option (Fin L) => o.elim (1 : ℝ) (fun _ => 0)) ∘ e, ?_⟩
      rw [x8_form_sub, hfA]
      simp only [Function.comp_def, Equiv.apply_symm_apply, Option.elim]
      rw [show (fun _ : Fin L => (0:ℝ)) = 0 from rfl, mulVec_zero]
      simp
    obtain ⟨lam, hlam, hP⟩ := (ModernConvex.SLemma.s_lemma _ _ hA' hB' hfeas).mp (by
      intro x hx
      rw [x8_form_sub] at hx ⊢
      exact key _ hx)
    refine ⟨lam, hlam, ?_⟩
    have hsub : B.submatrix e e - lam • A.submatrix e e = (B - lam • A).submatrix e e := by
      ext i j; simp
    rw [hsub, posSemidef_submatrix_equiv] at hP
    convert hP using 1
    rw [hAd, hBd]
    ext p q
    cases p <;> cases q <;> simp [momentBlock] <;> ring
  · rintro ⟨lam, hlam, hP⟩ z hz
    have := hP.dotProduct_mulVec_nonneg (fun o => o.elim 1 z)
    have h1 := x8_qf_block (c - lam) v (fun l h => W l h + lam * G l h) (fun o => o.elim 1 z)
    rw [star_trivial, h1] at this
    simp only [Option.elim] at this
    have hsplit : ∑ l, ∑ h, (W l h + lam * G l h) * z l * z h =
        ∑ l, ∑ h, W l h * z l * z h + lam * ∑ l, ∑ h, G l h * z l * z h := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsplit, ← x8_normQ] at this
    have hz' : ∑ i, (Q *ᵥ z) i ^ 2 ≤ 1 := hz
    nlinarith [mul_le_mul_of_nonneg_left hz' hlam]

end X8Q


open Matrix RobustOpt2009.Adjustable

namespace X8Q

variable {L r n m : ℕ} {k : Fin n → ℕ}

lemma x8_sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ d, ∑ b, F a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

lemma x8_lin (D : Model L r n m k) (y : CoeffIndex k → ℝ) (j : Fin n) (z : Fin L → ℝ) :
    ∑ a, linearCoeff y j a * (D.P j).mulVec z a = ∑ l, pulledLinear D y j l * z l := by
  simp only [pulledLinear, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma x8_quad (D : Model L r n m k) (y : CoeffIndex k → ℝ) (j : Fin n) (z : Fin L → ℝ) :
    ∑ a, ∑ b, quadCoeff y j a b * (D.P j).mulVec z a * (D.P j).mulVec z b =
      ∑ l, ∑ h, pulledQuadratic D y j l h * z l * z h := by
  set X := (D.P j).mulVec z
  have hsym : ∑ a, ∑ b, quadCoeff y j a b * X a * X b =
      ∑ a, ∑ b, ((quadCoeff y j a b + quadCoeff y j b a) / 2) * X a * X b := by
    have h2 : ∑ a, ∑ b, quadCoeff y j b a * X a * X b = ∑ a, ∑ b, quadCoeff y j a b * X a * X b := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have : ∑ a, ∑ b, ((quadCoeff y j a b + quadCoeff y j b a) / 2) * X a * X b =
        (∑ a, ∑ b, quadCoeff y j a b * X a * X b + ∑ a, ∑ b, quadCoeff y j b a * X a * X b) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun _ _ => ?_
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this, h2]; ring
  rw [hsym]
  simp only [X, pulledQuadratic, mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [x8_sum4, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma x8_policy (D : Model L r n m k) (y : CoeffIndex k → ℝ) (z : Fin L → ℝ) (j : Fin n) :
    policy D y z j = constantCoeff y j + ∑ l, pulledLinear D y j l * z l +
      ∑ l, ∑ h, pulledQuadratic D y j l h * z l * z h := by
  rw [policy, x8_lin, x8_quad]

lemma x8_term (D : Model L r n m k) (y : CoeffIndex k → ℝ) (j : Fin n) (z : Fin L → ℝ)
    (r0 : ℝ) (r1 : Fin L → ℝ) (hfr : D.P j = 0 ∨ ∀ l, r1 l = 0) :
    (r0 + ∑ l, z l * r1 l) * policy D y z j = r0 * constantCoeff y j +
      ∑ l, (r0 * pulledLinear D y j l + r1 l * constantCoeff y j) * z l +
      ∑ l, ∑ h, r0 * pulledQuadratic D y j l h * z l * z h := by
  rw [x8_policy]
  rcases hfr with hP | hr
  · have hL : ∀ l, pulledLinear D y j l = 0 := by
      intro l; simp [pulledLinear, hP]
    have hQ : ∀ l h, pulledQuadratic D y j l h = 0 := by
      intro l h; simp [pulledQuadratic, hP]
    simp only [hL, hQ, zero_mul, Finset.sum_const_zero, add_zero, mul_zero, zero_add]
    rw [add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [hr, mul_zero, Finset.sum_const_zero, add_zero, zero_mul]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · congr 1; exact Finset.sum_congr rfl fun _ _ => by ring
    · exact Finset.sum_congr rfl fun _ _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

lemma x8_row (D : Model L r n m k) (hrec : FixedRecourse D) (t : ℝ) (y : CoeffIndex k → ℝ)
    (ρ : Row m) (z : Fin L → ℝ) :
    (∑ j, (rowCoeff0 D ρ j + ∑ l, z l * rowCoeff1 D ρ l j) * policy D y z j) +
        rowOffset0 D t ρ + ∑ l, z l * rowOffset1 D ρ l =
      residualConstant D t y ρ + ∑ l, residualLinear D y ρ l * z l +
        ∑ l, ∑ h, residualQuadratic D y ρ l h * z l * z h := by
  have hfr : ∀ j, D.P j = 0 ∨ ∀ l, rowCoeff1 D ρ l j = 0 := by
    intro j
    by_cases hP : D.P j = 0
    · exact Or.inl hP
    · right; intro l
      obtain ⟨h1, h2⟩ := hrec j hP l
      cases ρ with
      | none => simp [rowCoeff1, h1]
      | some i => simp [rowCoeff1, h2 i]
  rw [Finset.sum_congr rfl fun j _ => x8_term D y j z _ _ (hfr j)]
  simp only [Finset.sum_add_distrib]
  simp only [residualConstant, residualLinear, residualQuadratic, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul]
  rw [Finset.sum_comm (f := fun j l => rowCoeff0 D ρ j * pulledLinear D y j l * z l),
    Finset.sum_comm (f := fun j l => rowCoeff1 D ρ l j * constantCoeff y j * z l)]
  have hq : ∑ j, ∑ l, ∑ h, rowCoeff0 D ρ j * pulledQuadratic D y j l h * z l * z h =
      ∑ l, ∑ h, ∑ j, rowCoeff0 D ρ j * pulledQuadratic D y j l h * z l * z h := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [hq]
  have ho : ∑ l, z l * rowOffset1 D ρ l = ∑ l, rowOffset1 D ρ l * z l :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [ho]
  ring

end X8Q


open Matrix RobustOpt2009.Adjustable

namespace X8Q

variable {L r n m : ℕ} {k : Fin n → ℕ}

lemma x8_epi (D : Model L r n m k) (hrec : FixedRecourse D) (t : ℝ) (y : CoeffIndex k → ℝ) :
    robustEpigraph D t y ↔ ∀ ρ : Row m, ∀ z ∈ ellipsoid D.Q,
      0 ≤ residualConstant D t y ρ + ∑ l, residualLinear D y ρ l * z l +
        ∑ l, ∑ h, residualQuadratic D y ρ l h * z l * z h := by
  have hn : ∀ z, residualConstant D t y none + ∑ l, residualLinear D y none l * z l +
      ∑ l, ∑ h, residualQuadratic D y none l h * z l * z h =
      t - ((∑ j, (D.c0 j + ∑ l, z l * D.c1 l j) * policy D y z j) + D.d0 +
        ∑ l, z l * D.d1 l) := by
    intro z
    rw [← x8_row D hrec t y none z]
    have h1 : ∀ j, (rowCoeff0 D none j + ∑ l, z l * rowCoeff1 D none l j) * policy D y z j =
        -((D.c0 j + ∑ l, z l * D.c1 l j) * policy D y z j) := by
      intro j
      simp only [rowCoeff0, rowCoeff1, mul_neg, Finset.sum_neg_distrib]
      ring
    rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_neg_distrib]
    simp only [rowOffset0, rowOffset1, mul_neg, Finset.sum_neg_distrib]
    ring
  have hs : ∀ i z, residualConstant D t y (some i) + ∑ l, residualLinear D y (some i) l * z l +
      ∑ l, ∑ h, residualQuadratic D y (some i) l h * z l * z h =
      (∑ j, (D.A0 i j + ∑ l, z l * D.A1 l i j) * policy D y z j) -
        (D.b0 i + ∑ l, z l * D.b1 l i) := by
    intro i z
    rw [← x8_row D hrec t y (some i) z]
    simp only [rowCoeff0, rowCoeff1, rowOffset0, rowOffset1, mul_neg, Finset.sum_neg_distrib]
    ring
  constructor
  · intro h ρ z hz
    cases ρ with
    | none => rw [hn]; linarith [(h z hz).1]
    | some i => rw [hs]; linarith [(h z hz).2 i]
  · intro h z hz
    refine ⟨?_, fun i => ?_⟩
    · have := h none z hz; rw [hn] at this; linarith
    · have := h (some i) z hz; rw [hs] at this; linarith

lemma x8_rq_symm (D : Model L r n m k) (y : CoeffIndex k → ℝ) (ρ : Row m) :
    Matrix.transpose (fun l h => residualQuadratic D y ρ l h : Matrix (Fin L) (Fin L) ℝ) =
      fun l h => residualQuadratic D y ρ l h := by
  ext l h
  show residualQuadratic D y ρ h l = residualQuadratic D y ρ l h
  simp only [residualQuadratic, pulledQuadratic]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma x8_feas_iff (D : Model L r n m k) (hQ : Function.Injective D.Q.mulVec)
    (hrec : FixedRecourse D) (t : ℝ) (y : CoeffIndex k → ℝ) :
    robustEpigraph D t y ↔ ∃ lam : Row m → ℝ, sdpFeasible D (assemble t y lam) := by
  rw [x8_epi D hrec]
  have key : ∀ ρ : Row m, (∀ z ∈ ellipsoid D.Q,
      0 ≤ residualConstant D t y ρ + ∑ l, residualLinear D y ρ l * z l +
        ∑ l, ∑ h, residualQuadratic D y ρ l h * z l * z h) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ (momentBlock (residualConstant D t y ρ - lam)
        (fun l => residualLinear D y ρ l / 2)
        (fun l h => residualQuadratic D y ρ l h + lam * (D.Q.transpose * D.Q) l h)).PosSemidef := by
    intro ρ
    rw [← x8_ell D.Q hQ _ _ _ (x8_rq_symm D y ρ)]
    refine forall₂_congr fun z _ => ?_
    have : 2 * ∑ l, residualLinear D y ρ l / 2 * z l = ∑ l, residualLinear D y ρ l * z l := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this]
  constructor
  · intro h
    choose lam hlam using fun ρ => (key ρ).mp (h ρ)
    exact ⟨lam, fun ρ => (hlam ρ).1, fun ρ => (hlam ρ).2⟩
  · rintro ⟨lam, h1, h2⟩ ρ
    exact (key ρ).mpr ⟨lam ρ, h1 ρ, h2 ρ⟩

lemma x8_assemble_eta (u : VarIndex k m → ℝ) :
    assemble (threshold u) (coefficients u) (multiplier u) = u := by
  funext x
  rcases x with _ | a | i <;> rfl

end X8Q


open Matrix RobustOpt2009.Adjustable

namespace X8Q

variable {L r n m : ℕ} {k : Fin n → ℕ}

lemma x8_aff_cert (D : Model L r n m k) (u v : VarIndex k m → ℝ) (a b : ℝ) (hab : a + b = 1)
    (i : Row m) :
    certificateMatrix D (a • u + b • v) i =
      a • certificateMatrix D u i + b • certificateMatrix D v i := by
  set y1 := coefficients u
  set y2 := coefficients v
  have hC : coefficients (a • u + b • v) = a • y1 + b • y2 := rfl
  have hT : threshold (a • u + b • v) = a * threshold u + b * threshold v := rfl
  have hM : multiplier (a • u + b • v) i = a * multiplier u i + b * multiplier v i := rfl
  have hcc : ∀ j, constantCoeff (a • y1 + b • y2) j = a * constantCoeff y1 j + b * constantCoeff y2 j :=
    fun j => rfl
  have hpl : ∀ j l, pulledLinear D (a • y1 + b • y2) j l =
      a * pulledLinear D y1 j l + b * pulledLinear D y2 j l := by
    intro j l
    simp only [pulledLinear, linearCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hpq : ∀ j l h, pulledQuadratic D (a • y1 + b • y2) j l h =
      a * pulledQuadratic D y1 j l h + b * pulledQuadratic D y2 j l h := by
    intro j l h
    simp only [pulledQuadratic, quadCoeff, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hoff : ∀ t1 t2, rowOffset0 D (a * t1 + b * t2) i =
      a * rowOffset0 D t1 i + b * rowOffset0 D t2 i := by
    intro t1 t2
    cases i with
    | none => simp only [rowOffset0]; linear_combination D.d0 * hab
    | some i => simp only [rowOffset0]; linear_combination (D.b0 i) * hab
  have hrc : residualConstant D (threshold (a • u + b • v)) (coefficients (a • u + b • v)) i =
      a * residualConstant D (threshold u) y1 i + b * residualConstant D (threshold v) y2 i := by
    rw [hT, hC]
    simp only [residualConstant, hoff, hcc]
    have : ∀ j, rowCoeff0 D i j * (a * constantCoeff y1 j + b * constantCoeff y2 j) =
        a * (rowCoeff0 D i j * constantCoeff y1 j) + b * (rowCoeff0 D i j * constantCoeff y2 j) :=
      fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    ring
  have hrl : ∀ l, residualLinear D (coefficients (a • u + b • v)) i l =
      a * residualLinear D y1 i l + b * residualLinear D y2 i l := by
    intro l
    rw [hC]
    simp only [residualLinear, hpl, hcc]
    have : ∀ j, rowCoeff0 D i j * (a * pulledLinear D y1 j l + b * pulledLinear D y2 j l) +
        rowCoeff1 D i l j * (a * constantCoeff y1 j + b * constantCoeff y2 j) =
        a * (rowCoeff0 D i j * pulledLinear D y1 j l + rowCoeff1 D i l j * constantCoeff y1 j) +
        b * (rowCoeff0 D i j * pulledLinear D y2 j l + rowCoeff1 D i l j * constantCoeff y2 j) :=
      fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    linear_combination (-rowOffset1 D i l) * hab
  have hrq : ∀ l h, residualQuadratic D (coefficients (a • u + b • v)) i l h =
      a * residualQuadratic D y1 i l h + b * residualQuadratic D y2 i l h := by
    intro l h
    rw [hC]
    simp only [residualQuadratic, hpq, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  ext p q
  cases p <;> cases q <;>
    simp only [certificateMatrix, momentBlock, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  · rw [hrc, hM]; ring
  · rw [hrl]; ring
  · rw [hrl]; ring
  · rw [hrq, hM]; ring

lemma x8_card : Fintype.card (VarIndex k m) = 1 + (∑ j, (1 + k j + (k j) ^ 2)) + (m + 1) := by
  simp only [VarIndex, CoeffIndex, Row, Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_option, sq]
  ring

lemma x8_card_le : Fintype.card (VarIndex k m) ≤ variableBound k m := by
  rw [x8_card, variableBound]
  have : ∑ j, (1 + k j + k j ^ 2) ≤ ∑ _j : Fin n, (1 + observationSize k + observationSize k ^ 2) := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hk : k j ≤ observationSize k := by
      unfold observationSize
      exact Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have := Nat.pow_le_pow_left hk 2
    omega
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

theorem x8_main (k : Fin n → ℕ) (D : Model L r n m k)
    (hQ : Function.Injective D.Q.mulVec) (hrec : FixedRecourse D) :
    (∀ (t : ℝ) (y : CoeffIndex k → ℝ), robustEpigraph D t y ↔
      ∃ lam : Row m → ℝ, sdpFeasible D (assemble t y lam)) ∧
    {t : ℝ | ∃ y : CoeffIndex k → ℝ, robustEpigraph D t y} =
      threshold '' {u : VarIndex k m → ℝ | sdpFeasible D u} ∧
    (∀ (t : ℝ) (y : CoeffIndex k → ℝ), robustOptimal D t y ↔
      ∃ lam : Row m → ℝ, sdpOptimal D (assemble t y lam)) ∧
    (∀ (u v : VarIndex k m → ℝ) (a b : ℝ), a + b = 1 → ∀ i,
      certificateMatrix D (a • u + b • v) i =
        a • certificateMatrix D u i + b • certificateMatrix D v i) ∧
    Fintype.card (VarIndex k m) = 1 + (∑ j, (1 + k j + (k j) ^ 2)) + (m + 1) ∧
    Fintype.card (Row m) = m + 1 ∧
    Fintype.card (Option (Fin L)) = L + 1 ∧
    Fintype.card (VarIndex k m) ≤ variableBound k m ∧
    denseLMICoefficientCount L k m ≤
      (variableBound k m + 1) * (m + 1) * (L + 1) ^ 2 := by
  have h1 := x8_feas_iff D hQ hrec
  have hfeasv : ∀ v, sdpFeasible D v → robustEpigraph D (threshold v) (coefficients v) := by
    intro v hv
    rw [h1]
    exact ⟨multiplier v, by rw [x8_assemble_eta]; exact hv⟩
  refine ⟨h1, ?_, ?_, fun u v a b hab i => x8_aff_cert D u v a b hab i, x8_card, ?_, ?_,
    x8_card_le, ?_⟩
  · ext t
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨lam, hl⟩ := (h1 t y).mp hy
      exact ⟨_, hl, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, hfeasv u hu⟩
  · intro t y
    constructor
    · rintro ⟨hy, hopt⟩
      obtain ⟨lam, hl⟩ := (h1 t y).mp hy
      exact ⟨lam, hl, fun v hv => hopt _ _ (hfeasv v hv)⟩
    · rintro ⟨lam, hl, hopt⟩
      refine ⟨(h1 t y).mpr ⟨lam, hl⟩, fun s y' hs => ?_⟩
      obtain ⟨lam', hl'⟩ := (h1 s y').mp hs
      exact hopt _ hl'
  · simp [Row]
  · simp
  · unfold denseLMICoefficientCount
    have h2 : Fintype.card (Row m) = m + 1 := by simp [Row]
    have h3 : Fintype.card (Option (Fin L)) = L + 1 := by simp
    rw [h2, h3]
    have := x8_card_le (k := k) (m := m)
    gcongr

end X8Q

open RobustOpt2009.Adjustable in
theorem solution {L r n m : ℕ} (k : Fin n → ℕ) (D : Model L r n m k)
    (hQ : Function.Injective D.Q.mulVec) (hrec : FixedRecourse D) :
    (∀ (t : ℝ) (y : CoeffIndex k → ℝ), robustEpigraph D t y ↔
      ∃ lam : Row m → ℝ, sdpFeasible D (assemble t y lam)) ∧
    {t : ℝ | ∃ y : CoeffIndex k → ℝ, robustEpigraph D t y} =
      threshold '' {u : VarIndex k m → ℝ | sdpFeasible D u} ∧
    (∀ (t : ℝ) (y : CoeffIndex k → ℝ), robustOptimal D t y ↔
      ∃ lam : Row m → ℝ, sdpOptimal D (assemble t y lam)) ∧
    (∀ (u v : VarIndex k m → ℝ) (a b : ℝ), a + b = 1 → ∀ i,
      certificateMatrix D (a • u + b • v) i =
        a • certificateMatrix D u i + b • certificateMatrix D v i) ∧
    Fintype.card (VarIndex k m) = 1 + (∑ j, (1 + k j + (k j) ^ 2)) + (m + 1) ∧
    Fintype.card (Row m) = m + 1 ∧
    Fintype.card (Option (Fin L)) = L + 1 ∧
    Fintype.card (VarIndex k m) ≤ variableBound k m ∧
    denseLMICoefficientCount L k m ≤
      (variableBound k m + 1) * (m + 1) * (L + 1) ^ 2 :=
  X8Q.x8_main k D hQ hrec
