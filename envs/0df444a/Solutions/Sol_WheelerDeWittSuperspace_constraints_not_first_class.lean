-- Prove2me | solution 1 for WheelerDeWittSuperspace.constraints_not_first_class
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T22:24:40.062849+00:00
-- url     : https://prove2.me/submissions/0c900398-e03d-44ac-ae65-99e5f4a1d0e6

import Definitions.Def_WheelerDeWittSuperspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false

open Matrix MatrixOrder

namespace WheelerDeWittSuperspace

noncomputable section

local notation "M3" => Matrix (Fin 3) (Fin 3) ℝ

/-- Frobenius pairing of two `3 × 3` arrays. -/
def frob (u v : M3) : ℝ := ∑ a, ∑ b, u a b * v a b

/-- The DeWitt bilinear form `G_m(u, v)`. -/
def gform (m u v : M3) : ℝ := ∑ a, ∑ b, ∑ c, ∑ d, deWitt m a b c d * u a b * v c d

/-- Elementary matrix `E_ab`. -/
def ee (a b : Fin 3) : M3 := of fun i j => if i = a ∧ j = b then 1 else 0

theorem gform_eq (m u v : M3) : gform m u v =
    (frob u (m * v * mᵀ) + frob u (m * vᵀ * mᵀ) - frob m u * frob m v) / (2 * volume m) := by
  simp only [gform, frob, deWitt, Fin.sum_univ_three, mul_apply, transpose_apply]; ring

theorem frob_adj (X Y Z W : M3) : frob X (Y * Z * W) = frob (Yᵀ * X * Wᵀ) Z := by
  simp only [frob, Fin.sum_univ_three, mul_apply, transpose_apply]; ring

theorem frob_comm (u v : M3) : frob u v = frob v u := by
  simp only [frob, Fin.sum_univ_three]; ring

theorem frob_one (P : M3) : frob P 1 = trace P := by
  simp [frob, Fin.sum_univ_three, trace, one_apply]

theorem frob_transpose (X P : M3) : frob Xᵀ P = frob X Pᵀ := by
  simp only [frob, Fin.sum_univ_three, transpose_apply]; ring

theorem frob_add_left (X Y P : M3) : frob (X + Y) P = frob X P + frob Y P := by
  simp only [frob, Fin.sum_univ_three, Matrix.add_apply]; ring

theorem frob_comb (X E : M3) (s β : ℝ) :
    frob X (s • 1 + β • E) = s * trace X + β * frob X E := by
  simp [frob, trace, Fin.sum_univ_three, one_apply]; ring

theorem trace_comb (E : M3) (s β : ℝ) : trace (s • 1 + β • E) = 3 * s + β * trace E := by
  simp [trace, Fin.sum_univ_three, one_apply]; ring

theorem gform_neg_left (m u v : M3) : gform m (-u) v = -gform m u v := by
  simp only [gform, Fin.sum_univ_three, Matrix.neg_apply]; ring

theorem gform_neg_right (m u v : M3) : gform m u (-v) = -gform m u v := by
  simp only [gform, Fin.sum_univ_three, Matrix.neg_apply]; ring

theorem frob_self_pos (X : M3) (h : ∃ a b, X a b ≠ 0) : 0 < frob X X := by
  obtain ⟨a, b, h⟩ := h
  unfold frob
  calc 0 < X a b * X a b := mul_self_pos.2 h
    _ ≤ ∑ j, X a j * X a j :=
        Finset.single_le_sum (f := fun j => X a j * X a j) (fun j _ => mul_self_nonneg _)
          (Finset.mem_univ b)
    _ ≤ ∑ i, ∑ j, X i j * X i j :=
        Finset.single_le_sum (f := fun i => ∑ j, X i j * X i j)
          (fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _) (Finset.mem_univ a)

/-- In the frame `m = Bᵀ B`, the DeWitt quadratic form of `q = B⁻¹ P B⁻ᵀ` is the flat one. -/
theorem frame_quad (B Bi P : M3) (hBBi : B * Bi = 1) (hP : Pᵀ = P) :
    gform (Bᵀ * B) (Bi * P * Biᵀ) (Bi * P * Biᵀ) =
      (2 * frob P P - trace P ^ 2) / (2 * volume (Bᵀ * B)) := by
  have hBt : Biᵀ * Bᵀ = 1 := by rw [← transpose_mul, hBBi, transpose_one]
  have key : B * (Bi * P * Biᵀ) * Bᵀ = P := by
    simp only [← Matrix.mul_assoc, hBBi, Matrix.one_mul]
    rw [Matrix.mul_assoc, hBt, Matrix.mul_one]
  have hq : (Bi * P * Biᵀ)ᵀ = Bi * P * Biᵀ := by
    simp [transpose_mul, hP, Matrix.mul_assoc]
  have hm : (Bᵀ * B)ᵀ = Bᵀ * B := by simp [transpose_mul]
  have e1 : Bᵀ * B * (Bi * P * Biᵀ) * (Bᵀ * B) = Bᵀ * P * B := by
    conv_rhs => rw [← key]
    simp only [Matrix.mul_assoc]
  have f1 : frob (Bi * P * Biᵀ) (Bᵀ * P * B) = frob P P := by
    rw [frob_adj, transpose_transpose, key]
  have f2 : frob (Bᵀ * B) (Bi * P * Biᵀ) = trace P := by
    rw [frob_comm, show Bᵀ * B = Bᵀ * 1 * B by simp, frob_adj, transpose_transpose, key,
      frob_one]
  rw [gform_eq, hq, hm, e1, f1, f2]; ring

/-- The linear term in the same frame. -/
theorem frame_lin (B Bi P D : M3) (hBBi : B * Bi = 1) (hP : Pᵀ = P) :
    gform (Bᵀ * B) D (Bi * P * Biᵀ) + gform (Bᵀ * B) (Bi * P * Biᵀ) D =
      (2 * frob (B * (D + Dᵀ) * Bᵀ) P - trace (B * (D + Dᵀ) * Bᵀ) * trace P) /
        (2 * volume (Bᵀ * B)) := by
  have hBt : Biᵀ * Bᵀ = 1 := by rw [← transpose_mul, hBBi, transpose_one]
  have key : B * (Bi * P * Biᵀ) * Bᵀ = P := by
    simp only [← Matrix.mul_assoc, hBBi, Matrix.one_mul]
    rw [Matrix.mul_assoc, hBt, Matrix.mul_one]
  have hq : (Bi * P * Biᵀ)ᵀ = Bi * P * Biᵀ := by
    simp [transpose_mul, hP, Matrix.mul_assoc]
  have hm : (Bᵀ * B)ᵀ = Bᵀ * B := by simp [transpose_mul]
  have e1 : Bᵀ * B * (Bi * P * Biᵀ) * (Bᵀ * B) = Bᵀ * P * B := by
    conv_rhs => rw [← key]
    simp only [Matrix.mul_assoc]
  set Y := B * D * Bᵀ with hY
  have f2 : frob (Bᵀ * B) (Bi * P * Biᵀ) = trace P := by
    rw [frob_comm, show Bᵀ * B = Bᵀ * 1 * B by simp, frob_adj, transpose_transpose, key,
      frob_one]
  have g1 : frob D (Bᵀ * P * B) = frob Y P := by rw [frob_adj, transpose_transpose]
  have g2 : frob (Bᵀ * B) D = trace Y := by
    rw [frob_comm, show Bᵀ * B = Bᵀ * 1 * B by simp, frob_adj, transpose_transpose, frob_one]
  have g3 : frob (Bi * P * Biᵀ) (Bᵀ * B * D * (Bᵀ * B)) = frob Y P := by
    rw [show Bᵀ * B * D * (Bᵀ * B) = Bᵀ * Y * B by simp only [hY, Matrix.mul_assoc],
      frob_adj, transpose_transpose, key, frob_comm]
  have g4 : frob (Bi * P * Biᵀ) (Bᵀ * B * Dᵀ * (Bᵀ * B)) = frob Y P := by
    rw [show Bᵀ * B * Dᵀ * (Bᵀ * B) = Bᵀ * Yᵀ * B by
        simp only [hY, transpose_mul, transpose_transpose, Matrix.mul_assoc],
      frob_adj, transpose_transpose, key, frob_comm, frob_transpose, hP]
  have hT : B * (D + Dᵀ) * Bᵀ = Y + Yᵀ := by
    simp only [hY, Matrix.mul_add, Matrix.add_mul, transpose_mul, transpose_transpose,
      Matrix.mul_assoc]
  have g5 : frob Yᵀ P = frob Y P := by rw [frob_transpose, hP]
  rw [gform_eq, gform_eq, hq, hm, e1, g1, g2, f2, g3, g4,
    hT, frob_add_left, g5, trace_add, trace_transpose]
  ring

/-- Flat-frame existence with an auxiliary traceless direction `E`. -/
theorem ident_aux (T E : M3) (hE : Eᵀ = E) (htrE : trace E = 0) (hEpos : 0 < frob E E)
    (hTE : trace T ≠ 0 ∨ frob T E ≠ 0) (C : ℝ) :
    ∃ P : M3, Pᵀ = P ∧ 2 * frob P P - trace P ^ 2 = C ∧
      2 * frob T P - trace T * trace P ≠ 0 := by
  have hC := le_abs_self C
  set α := Real.sqrt ((|C| + 1 - C) / 3) with hαdef
  set β := Real.sqrt ((|C| + 1) / (2 * frob E E)) with hβdef
  have hα : α ^ 2 = (|C| + 1 - C) / 3 := Real.sq_sqrt (by linarith)
  have hβ : β ^ 2 = (|C| + 1) / (2 * frob E E) := Real.sq_sqrt (by positivity)
  have hαpos : 0 < α := Real.sqrt_pos.2 (by linarith)
  have hβpos : 0 < β := Real.sqrt_pos.2 (by positivity)
  have sym : ∀ s : ℝ, (s • (1 : M3) + β • E)ᵀ = s • 1 + β • E := by
    intro s; simp [transpose_add, transpose_smul, hE]
  have quad : ∀ s : ℝ, 2 * frob (s • (1 : M3) + β • E) (s • 1 + β • E) -
      trace (s • (1 : M3) + β • E) ^ 2 = C ↔ 2 * β ^ 2 * frob E E - 3 * s ^ 2 = C := by
    intro s
    rw [frob_comb, frob_comm _ E, frob_comb, trace_comb, htrE]
    constructor <;> intro h <;> linarith
  have quadv : ∀ s : ℝ, s ^ 2 = α ^ 2 → 2 * β ^ 2 * frob E E - 3 * s ^ 2 = C := by
    intro s hs; rw [hs, hα, hβ]; field_simp; ring
  have lin : ∀ s : ℝ, 2 * frob T (s • (1 : M3) + β • E) - trace T * trace (s • 1 + β • E) =
      2 * β * frob T E - s * trace T := by
    intro s; rw [frob_comb, trace_comb, htrE]; ring
  by_cases h1 : 2 * β * frob T E - α * trace T = 0
  · refine ⟨(-α) • 1 + β • E, sym _, (quad _).2 (quadv _ (by ring)), ?_⟩
    rw [lin]
    intro h2
    rcases hTE with h | h
    · exact h (by nlinarith)
    · exact h (by nlinarith)
  · exact ⟨α • 1 + β • E, sym _, (quad _).2 (quadv _ rfl), by rw [lin]; exact h1⟩

theorem ident_exists (T : M3) (hT : Tᵀ = T) (hpos : 0 < frob T T) (C : ℝ) :
    ∃ P : M3, Pᵀ = P ∧ 2 * frob P P - trace P ^ 2 = C ∧
      2 * frob T P - trace T * trace P ≠ 0 := by
  by_cases htr : trace T = 0
  · exact ident_aux T T hT htr hpos (Or.inr hpos.ne') C
  · refine ident_aux T !![1, 0, 0; 0, -1, 0; 0, 0, 0] ?_ ?_ ?_ (Or.inl htr) C
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · simp [trace, Fin.sum_univ_three]
    · simp only [frob, Fin.sum_univ_three, of_apply, cons_val, cons_val_zero, cons_val_one, head_cons, tail_cons, cons_val_two]; norm_num

/-- Key algebraic lemma: on every level set of the DeWitt form at a positive-definite `m`,
the linear functional `q ↦ G(D, q) + G(q, D)` is not identically zero when `D + Dᵀ ≠ 0`. -/
theorem exists_level (m D : M3) (hm : m.PosDef) (hD : ∃ a b, D a b + D b a ≠ 0) (c : ℝ) :
    ∃ q : M3, gform m q q = c ∧ gform m D q + gform m q D ≠ 0 := by
  have hdet : 0 < m.det := hm.det_pos
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hm.posSemidef.nonneg
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hB
  subst hB
  have hdetB : IsUnit B.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [det_mul, det_transpose, h0, mul_zero] at hdet
    exact lt_irrefl _ hdet
  have hBBi : B * B⁻¹ = 1 := mul_nonsing_inv B hdetB
  have hBiB : B⁻¹ * B = 1 := nonsing_inv_mul B hdetB
  have hV : 0 < volume (Bᵀ * B) := Real.sqrt_pos.2 hdet
  set T := B * (D + Dᵀ) * Bᵀ with hTdef
  have hT : Tᵀ = T := by
    simp only [hTdef, transpose_mul, transpose_add, transpose_transpose, Matrix.mul_assoc]
    rw [add_comm]
  have hTpos : 0 < frob T T := by
    apply frob_self_pos
    by_contra hcon
    push Not at hcon
    have hT0 : T = 0 := by ext i j; exact hcon i j
    obtain ⟨a, b, hab⟩ := hD
    have hBt : Bᵀ * B⁻¹ᵀ = 1 := by rw [← transpose_mul, hBiB, transpose_one]
    have hS : B⁻¹ * T * B⁻¹ᵀ = D + Dᵀ := by
      simp only [hTdef, ← Matrix.mul_assoc, hBiB, Matrix.one_mul]
      rw [Matrix.mul_assoc, hBt, Matrix.mul_one]
    rw [hT0, Matrix.mul_zero, Matrix.zero_mul] at hS
    apply hab
    have := congrFun (congrFun hS a) b
    simpa [transpose_apply] using this.symm
  obtain ⟨P, hP, hQ, hL⟩ := ident_exists T hT hTpos (c * (2 * volume (Bᵀ * B)))
  refine ⟨B⁻¹ * P * B⁻¹ᵀ, ?_, ?_⟩
  · rw [frame_quad B B⁻¹ P hBBi hP, hQ]; field_simp
  · rw [frame_lin B B⁻¹ P D hBBi hP]; exact div_ne_zero hL (by positivity)

section Calculus

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem hasDerivAt_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (w v : E)
    (hd : DifferentiableAt ℝ f w) :
    HasDerivAt (fun t : ℝ => f (w + t • v)) (fderiv ℝ f w v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have hd' : HasFDerivAt f (fderiv ℝ f w) (w + (0 : ℝ) • v) := by simpa using hd.hasFDerivAt
  exact hd'.comp_hasDerivAt (0 : ℝ) hl

theorem fderiv_apply_eq_zero_of_line_invariant' {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (w v : E)
    (hf : ∀ t : ℝ, f (w + t • v) = f w) : fderiv ℝ f w v = 0 := by
  by_cases hd : DifferentiableAt ℝ f w
  · have h1 := hasDerivAt_line f w v hd
    have h2 : HasDerivAt (fun t : ℝ => f (w + t • v)) 0 0 := by
      simp_rw [hf]; exact hasDerivAt_const _ _
    exact h1.unique h2
  · simp [fderiv_zero_of_not_differentiableAt hd]

theorem coordDir_apply_of_ne' {z x : X} (hzx : z ≠ x) (a b : Fin 3) :
    coordDir z a b x = 0 := by
  funext i j
  simp [coordDir, Ne.symm hzx]

theorem det_metricAt_differentiable (z : X) :
    Differentiable ℝ (fun h : Config X => (metricAt h z).det) := by
  simp only [metricAt, det_fin_three, of_apply]; fun_prop

theorem volume_diffAt (h : Config X) (z : X) (hpos : 0 < (metricAt h z).det) :
    DifferentiableAt ℝ (fun h' : Config X => volume (metricAt h' z)) h := by
  unfold volume
  exact (det_metricAt_differentiable z h).sqrt hpos.ne'

theorem deWitt_diffAt (h : Config X) (z : X) (hpos : 0 < (metricAt h z).det)
    (a b c d : Fin 3) :
    DifferentiableAt ℝ (fun h' : Config X => deWitt (metricAt h' z) a b c d) h := by
  have hv := volume_diffAt h z hpos
  have hne : 2 * volume (metricAt h z) ≠ 0 := by
    have : 0 < volume (metricAt h z) := Real.sqrt_pos.2 hpos
    positivity
  have hnum : DifferentiableAt ℝ (fun h' : Config X =>
      metricAt h' z a c * metricAt h' z b d + metricAt h' z a d * metricAt h' z b c -
        metricAt h' z a b * metricAt h' z c d) h := by
    simp only [metricAt, of_apply]; fun_prop
  simp only [deWitt, div_eq_mul_inv]
  exact hnum.mul ((hv.const_mul 2).inv hne)

theorem potential_diffAt (kappa Lam : ℝ) (R : Config X → X → ℝ)
    (hR : ∀ z, ContDiff ℝ 1 (fun h => R h z)) (h : Config X) (z : X)
    (hpos : 0 < (metricAt h z).det) :
    DifferentiableAt ℝ (fun h' : Config X => potentialAt kappa Lam R h' z) h := by
  have hv := volume_diffAt h z hpos
  have hr : DifferentiableAt ℝ (fun h' => R h' z) h := (hR z).differentiable_one h
  unfold potentialAt
  fun_prop

theorem constraint_diffAt (kappa Lam : ℝ) (R : Config X → X → ℝ)
    (hR : ∀ z, ContDiff ℝ 1 (fun h => R h z)) (w : Phase X) (z : X)
    (hpos : 0 < (metricAt w.1 z).det) :
    DifferentiableAt ℝ (classicalConstraint kappa Lam R z) w := by
  have hG : ∀ a b c d, DifferentiableAt ℝ
      (fun w' : Phase X => deWitt (metricAt w'.1 z) a b c d) w :=
    fun a b c d => (deWitt_diffAt w.1 z hpos a b c d).comp w differentiableAt_fst
  have hV : DifferentiableAt ℝ (fun w' : Phase X => potentialAt kappa Lam R w'.1 z) w :=
    (potential_diffAt kappa Lam R hR w.1 z hpos).comp w differentiableAt_fst
  have hp : ∀ a b, DifferentiableAt ℝ (fun w' : Phase X => w'.2 z a b) w := by
    intro a b; fun_prop
  unfold classicalConstraint
  fun_prop

theorem constraint_eq (kappa Lam : ℝ) (R : Config X → X → ℝ) (z : X) (w : Phase X) :
    classicalConstraint kappa Lam R z w =
      2 * kappa * gform (metricAt w.1 z) (w.2 z) (w.2 z) + potentialAt kappa Lam R w.1 z :=
  rfl

theorem gform_line (m u e : M3) (t : ℝ) :
    gform m (u + t • e) (u + t • e) =
      gform m u u + t * (gform m e u + gform m u e) + t ^ 2 * gform m e e := by
  simp only [gform, Fin.sum_univ_three, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring

theorem deriv_quad_unique {f : ℝ → ℝ} {f' : ℝ} (A G1 G2 V k : ℝ) (hf : HasDerivAt f f' 0)
    (heq : ∀ t, f t = k * (A + t * G1 + t ^ 2 * G2) + V) : f' = k * G1 := by
  obtain rfl : f = _ := funext heq
  have h2 := ((((hasDerivAt_id (0 : ℝ)).mul_const G1).const_add A).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const G2)).const_mul k |>.add_const V
  have := hf.unique h2
  simpa using this

/-- Momentum derivative of the constraint at its own site. -/
theorem fderiv_mom_self (kappa Lam : ℝ) (R : Config X → X → ℝ)
    (hR : ∀ z, ContDiff ℝ 1 (fun h => R h z)) (w : Phase X) (z : X)
    (hpos : 0 < (metricAt w.1 z).det) (a b : Fin 3) :
    fderiv ℝ (classicalConstraint kappa Lam R z) w (0, coordDir z a b) =
      2 * kappa * (gform (metricAt w.1 z) (ee a b) (w.2 z) +
        gform (metricAt w.1 z) (w.2 z) (ee a b)) := by
  have h1 := hasDerivAt_line _ w ((0 : Config X), coordDir z a b)
    (constraint_diffAt kappa Lam R hR w z hpos)
  refine deriv_quad_unique (gform (metricAt w.1 z) (w.2 z) (w.2 z)) _
    (gform (metricAt w.1 z) (ee a b) (ee a b)) (potentialAt kappa Lam R w.1 z) _ h1 fun t => ?_
  have e1 : (w + t • ((0 : Config X), coordDir z a b)).1 = w.1 := by simp
  have e2 : ((w + t • ((0 : Config X), coordDir z a b)).2 z : M3) = (show M3 from w.2 z) + t • ee a b := by
    ext i j; show _ = w.2 z i j + (t • ee a b) i j; simp [coordDir, ee]
  rw [constraint_eq, e1, e2, gform_line]

/-- Momentum derivative of the constraint at a different site vanishes. -/
theorem fderiv_mom_other (kappa Lam : ℝ) (R : Config X → X → ℝ) (w : Phase X) {z z' : X}
    (hzz : z' ≠ z) (a b : Fin 3) :
    fderiv ℝ (classicalConstraint kappa Lam R z) w (0, coordDir z' a b) = 0 := by
  refine fderiv_apply_eq_zero_of_line_invariant' _ w _ fun t => ?_
  simp [constraint_eq, coordDir_apply_of_ne' hzz]

/-- Metric derivative of the constraint at `z` along another site `z'` only sees the
potential. -/
theorem fderiv_metric_other (kappa Lam : ℝ) (R : Config X → X → ℝ)
    (hR : ∀ z, ContDiff ℝ 1 (fun h => R h z)) (w : Phase X) {z z' : X} (hzz : z' ≠ z)
    (hpos : 0 < (metricAt w.1 z).det) (a b : Fin 3) :
    fderiv ℝ (classicalConstraint kappa Lam R z) w (coordDir z' a b, 0) =
      partialR (fun h' => potentialAt kappa Lam R h' z) z' a b w.1 := by
  have h1 := hasDerivAt_line _ w (coordDir z' a b, (0 : Config X))
    (constraint_diffAt kappa Lam R hR w z hpos)
  have h2 := (hasDerivAt_line (fun h' => potentialAt kappa Lam R h' z) w.1 (coordDir z' a b)
    (potential_diffAt kappa Lam R hR w.1 z hpos)).const_add
      (2 * kappa * gform (metricAt w.1 z) (w.2 z) (w.2 z))
  have hline : ∀ t : ℝ, classicalConstraint kappa Lam R z (w + t • (coordDir z' a b, 0)) =
      2 * kappa * gform (metricAt w.1 z) (w.2 z) (w.2 z) +
        potentialAt kappa Lam R (w.1 + t • coordDir z' a b) z := by
    intro t
    have e1 : (w + t • (coordDir z' a b, (0 : Config X))).2 = w.2 := by simp
    have e2 : (w + t • (coordDir z' a b, (0 : Config X))).1 = w.1 + t • coordDir z' a b := by
      simp
    have e3 : metricAt (w.1 + t • coordDir z' a b) z = metricAt w.1 z := by
      simp [metricAt, coordDir_apply_of_ne' hzz]
    rw [constraint_eq, e1, e2, e3]
  rw [show (fun t : ℝ => classicalConstraint kappa Lam R z (w + t • (coordDir z' a b, 0))) =
    _ from funext hline] at h1
  exact h1.unique h2

/-- The bracket of the constraints at two distinct sites. -/
theorem bracket_formula (kappa Lam : ℝ) (R : Config X → X → ℝ)
    (hR : ∀ z, ContDiff ℝ 1 (fun h => R h z)) (h p : Config X) (hh : IsPhysical h)
    (x y : X) (hxy : x ≠ y) :
    poisson (classicalConstraint kappa Lam R x) (classicalConstraint kappa Lam R y) (h, p) =
      (∑ a, ∑ b, partialR (fun h' => potentialAt kappa Lam R h' x) y a b h *
          (2 * kappa * (gform (metricAt h y) (ee a b) (p y) +
            gform (metricAt h y) (p y) (ee a b)))) -
      ∑ a, ∑ b, 2 * kappa * (gform (metricAt h x) (ee a b) (p x) +
            gform (metricAt h x) (p x) (ee a b)) *
          partialR (fun h' => potentialAt kappa Lam R h' y) x a b h := by
  have hpos : ∀ z, 0 < (metricAt h z).det := fun z => (hh z).det_pos
  unfold poisson
  rw [Fintype.sum_eq_add x y hxy]
  · simp only [fderiv_mom_self kappa Lam R hR (h, p) x (hpos x),
      fderiv_mom_self kappa Lam R hR (h, p) y (hpos y),
      fderiv_mom_other kappa Lam R (h, p) hxy, fderiv_mom_other kappa Lam R (h, p) (Ne.symm hxy),
      fderiv_metric_other kappa Lam R hR (h, p) hxy (hpos y),
      fderiv_metric_other kappa Lam R hR (h, p) (Ne.symm hxy) (hpos x)]
    simp only [mul_zero, zero_mul, zero_sub, sub_zero, Finset.sum_neg_distrib]
    ring
  · rintro z ⟨hzx, hzy⟩
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [fderiv_mom_other kappa Lam R (h, p) hzx, fderiv_mom_other kappa Lam R (h, p) hzy]
    ring

theorem sum_mom (k : ℝ) (m P D : M3) :
    ∑ a, ∑ b, k * (gform m (ee a b) P + gform m P (ee a b)) * D a b =
      k * (gform m D P + gform m P D) := by
  simp [gform, ee, Fin.sum_univ_three]
  ring

theorem cnfc_main {X : Type*} [Fintype X] [DecidableEq X] (kappa Lam : ℝ)
    (hkappa : kappa ≠ 0) (R : Config X → X → ℝ) (hR : ∀ z, ContDiff ℝ 1 (fun h => R h z))
    (h : Config X) (hh : IsPhysical h) (x y : X) (hxy : x ≠ y)
    (hdep : ∃ a b, partialR (fun h' => potentialAt kappa Lam R h' y) x a b h +
        partialR (fun h' => potentialAt kappa Lam R h' y) x b a h ≠ 0) :
    ∃ p : Config X, (∀ z, classicalConstraint kappa Lam R z (h, p) = 0) ∧
      poisson (classicalConstraint kappa Lam R x) (classicalConstraint kappa Lam R y) (h, p) ≠ 0 := by
  set c : X → ℝ := fun z => -potentialAt kappa Lam R h z / (2 * kappa) with hc
  set D : M3 := of fun a b => partialR (fun h' => potentialAt kappa Lam R h' y) x a b h with hD
  obtain ⟨P, hPq, hPl⟩ := exists_level (metricAt h x) D (hh x)
    (by obtain ⟨a, b, hab⟩ := hdep; exact ⟨a, b, by simpa [hD] using hab⟩) (c x)
  have hq : ∀ z, ∃ q : M3, gform (metricAt h z) q q = c z := fun z => by
    obtain ⟨q, hq, -⟩ := exists_level (metricAt h z) 1 (hh z) ⟨0, 0, by norm_num⟩ (c z)
    exact ⟨q, hq⟩
  choose q hq using hq
  have hcon : ∀ pp : Config X, (∀ z, gform (metricAt h z) (pp z) (pp z) = c z) →
      ∀ z, classicalConstraint kappa Lam R z (h, pp) = 0 := by
    intro pp hpp z
    rw [constraint_eq]
    simp only
    rw [hpp z, hc]
    field_simp
    ring
  set p : Config X := fun z => if z = x then P else q z with hp
  set p' : Config X := fun z => if z = x then -P else q z with hp'
  have hpy : p y = q y := show (if y = x then P else q y) = q y from if_neg (Ne.symm hxy)
  have hp'y : p' y = q y := show (if y = x then -P else q y) = q y from if_neg (Ne.symm hxy)
  have hpx : p x = P := show (if x = x then P else q x) = P from if_pos rfl
  have hp'x : p' x = -P := show (if x = x then -P else q x) = -P from if_pos rfl
  have hcp : ∀ z, classicalConstraint kappa Lam R z (h, p) = 0 := by
    refine hcon p fun z => ?_
    by_cases hz : z = x
    · subst hz; rw [hpx, hPq]
    · simp only [hp, hz, if_false]; exact hq z
  have hcp' : ∀ z, classicalConstraint kappa Lam R z (h, p') = 0 := by
    refine hcon p' fun z => ?_
    by_cases hz : z = x
    · subst hz; rw [hp'x, gform_neg_left, gform_neg_right, neg_neg, hPq]
    · simp only [hp', hz, if_false]; exact hq z
  have hsum : ∑ a, ∑ b, 2 * kappa * (gform (metricAt h x) (ee a b) P +
      gform (metricAt h x) P (ee a b)) * partialR (fun h' => potentialAt kappa Lam R h' y) x a b h
      = 2 * kappa * (gform (metricAt h x) D P + gform (metricAt h x) P D) :=
    sum_mom _ _ _ D
  have hsum' : ∑ a, ∑ b, 2 * kappa * (gform (metricAt h x) (ee a b) (-P) +
      gform (metricAt h x) (-P) (ee a b)) * partialR (fun h' => potentialAt kappa Lam R h' y) x a b h
      = 2 * kappa * (gform (metricAt h x) D (-P) + gform (metricAt h x) (-P) D) :=
    sum_mom _ _ _ D
  have hb := bracket_formula kappa Lam R hR h p hh x y hxy
  have hb' := bracket_formula kappa Lam R hR h p' hh x y hxy
  rw [hpy, hpx, hsum] at hb
  rw [hp'y, hp'x, hsum', gform_neg_left, gform_neg_right] at hb'
  by_cases h0 : poisson (classicalConstraint kappa Lam R x)
      (classicalConstraint kappa Lam R y) (h, p) = 0
  · refine ⟨p', hcp', fun h1 => hPl ?_⟩
    have h4 : 4 * kappa * (gform (metricAt h x) D P + gform (metricAt h x) P D) = 0 := by
      rw [hb] at h0; rw [hb'] at h1; linarith
    rcases mul_eq_zero.1 h4 with h5 | h5
    · exact absurd h5 (mul_ne_zero (by norm_num) hkappa)
    · exact h5
  · exact ⟨p, hcp, h0⟩

end Calculus

end

end WheelerDeWittSuperspace

open WheelerDeWittSuperspace

theorem solution {X : Type*} [Fintype X] [DecidableEq X] (kappa Lam : ℝ)
    (hkappa : kappa ≠ 0) (R : Config X → X → ℝ) (hR : ∀ z, ContDiff ℝ 1 (fun h => R h z))
    (h : Config X) (hh : IsPhysical h) (x y : X) (hxy : x ≠ y)
    (hdep : ∃ a b, partialR (fun h' => potentialAt kappa Lam R h' y) x a b h +
        partialR (fun h' => potentialAt kappa Lam R h' y) x b a h ≠ 0) :
    ∃ p : Config X, (∀ z, classicalConstraint kappa Lam R z (h, p) = 0) ∧
      poisson (classicalConstraint kappa Lam R x) (classicalConstraint kappa Lam R y) (h, p) ≠ 0 :=
  cnfc_main kappa Lam hkappa R hR h hh x y hxy hdep
