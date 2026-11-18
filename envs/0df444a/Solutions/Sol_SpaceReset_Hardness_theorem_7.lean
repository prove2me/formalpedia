-- Prove2me | solution 1 for SpaceReset.Hardness.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T17:33:45.546335+00:00
-- url     : https://prove2.me/submissions/62cd3b55-cea8-4c50-9711-a221df0f60ba

import Mathlib
import Definitions.Def_SpaceReset_Hardness_Quantum
import Definitions.Def_SpaceReset_Hardness_DiscardDevice


/- Module SpaceResetFidelityCore -/

/-! Finite matrix foundations, extracted from the accepted Prove2Me proof
of Uhlmann (submission e7f79aee-b42a-40df-9b8b-becca22296a9,
theorem c84df38e-32fb-41ea-8ea7-c4b571ce7f65, Apache-2.0).
Only the Mathlib-only matrix proofs are retained; the unrelated relative
entropy sections and paper-specific definition imports are omitted. -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

namespace CFCBasics
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma psd_re {X : Matrix I I ℂ} (h : X.PosSemidef) : 0 ≤ X.trace.re :=
  (Complex.nonneg_iff.mp h.trace_nonneg).1

lemma fin (X : Matrix I I ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ X) :=
  (Matrix.finite_real_spectrum (A := X)).continuousOn f

lemma cs (X Y : Matrix I I ℂ) :
    (Xᴴ * Y).trace.re + (Yᴴ * X).trace.re ≤ (Xᴴ * X).trace.re + (Yᴴ * Y).trace.re := by
  have h0 := psd_re (Matrix.posSemidef_conjTranspose_mul_self (X - Y))
  simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
    Complex.sub_re] at h0
  linarith

/-- `Re Tr Z ≤ Tr √(Z Z†)` -/
theorem re_tr_le (Z : Matrix I I ℂ) : Z.trace.re ≤ (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  set M := Z * Zᴴ
  have hM : M.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Z
  have hMs : IsSelfAdjoint M := hM.1.isSelfAdjoint
  have hspec : ∀ x ∈ spectrum ℝ M, 0 ≤ x := fun x hx => spectrum_nonneg_of_nonneg hM.nonneg hx
  have key : ∀ ε : ℝ, 0 < ε → Z.trace.re ≤ (cfc Real.sqrt M).trace.re + ε * Fintype.card I / 2 := by
    intro ε hε
    set L := cfc (fun x => Real.sqrt (Real.sqrt x + ε)) M
    set K := cfc (fun x => (Real.sqrt (Real.sqrt x + ε))⁻¹) M
    have hpos : ∀ x : ℝ, 0 < Real.sqrt (Real.sqrt x + ε) :=
      fun x => Real.sqrt_pos.2 (by positivity)
    have hLK : L * K = 1 := by
      rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => mul_inv_cancel₀ (hpos x).ne'
    have hKL : K * L = 1 := by
      rw [← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_const_one ℝ M]
      exact cfc_congr fun x _ => inv_mul_cancel₀ (hpos x).ne'
    have hLh : Lᴴ = L := (cfc_predicate _ M : IsSelfAdjoint L)
    have hKh : Kᴴ = K := (cfc_predicate _ M : IsSelfAdjoint K)
    have h := cs L (K * Z)
    have e1 : Lᴴ * (K * Z) = Z := by rw [hLh, ← Matrix.mul_assoc, hLK, Matrix.one_mul]
    have e2 : (K * Z)ᴴ * L = Zᴴ := by
      rw [conjTranspose_mul, hKh, Matrix.mul_assoc, hKL, Matrix.mul_one]
    have e3 : (Lᴴ * L).trace.re = (cfc Real.sqrt M).trace.re + ε * Fintype.card I := by
      have : Lᴴ * L = cfc Real.sqrt M + (ε : ℂ) • 1 := by
        rw [hLh, ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
        rw [show (ε : ℂ) • (1 : Matrix I I ℂ) = cfc (fun _ : ℝ => ε) M by
          rw [cfc_const ε M hMs]; simp [Algebra.algebraMap_eq_smul_one]]
        rw [← cfc_add _ _ _ (fin _ _) (fin _ _)]
        refine cfc_congr fun x hx => ?_
        exact Real.mul_self_sqrt (by have := Real.sqrt_nonneg x; linarith)
      rw [this, Matrix.trace_add, Complex.add_re, Matrix.trace_smul, Matrix.trace_one]
      simp
    have e4 : ((K * Z)ᴴ * (K * Z)).trace.re ≤ (cfc Real.sqrt M).trace.re := by
      have t1 : ((K * Z)ᴴ * (K * Z)).trace = (K * K * M).trace := by
        rw [conjTranspose_mul, hKh]
        rw [show Zᴴ * K * (K * Z) = Zᴴ * (K * K * Z) by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp only [M, Matrix.mul_assoc]
      have t2 : K * K * M = cfc (fun x => x / (Real.sqrt x + ε)) M := by
        rw [show K * K * M = K * K * cfc (fun x : ℝ => x) M by rw [cfc_id' ℝ M hMs],
          ← cfc_mul _ _ _ (fin _ _) (fin _ _), ← cfc_mul _ _ _ (fin _ _) (fin _ _)]
        refine cfc_congr fun x hx => ?_
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [← mul_inv, Real.mul_self_sqrt h1.le, div_eq_inv_mul]
      have t3 : (cfc Real.sqrt M - K * K * M).PosSemidef := by
        rw [t2, ← cfc_sub _ _ _ (fin _ _) (fin _ _)]
        refine (cfc_nonneg (fun x hx => ?_) :
          0 ≤ cfc (fun x => Real.sqrt x - x / (Real.sqrt x + ε)) M).posSemidef
        have h0 := hspec x hx
        have h1 : 0 < Real.sqrt x + ε := by positivity
        rw [sub_nonneg, div_le_iff₀ h1]
        have := Real.mul_self_sqrt h0
        nlinarith [Real.sqrt_nonneg x]
      have := psd_re t3
      rw [Matrix.trace_sub, Complex.sub_re] at this
      rw [t1]; linarith
    rw [e1, e2, e3, Matrix.trace_conjTranspose] at h
    simp only [RCLike.star_def, Complex.conj_re] at h
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have := key (2 * δ / (Fintype.card I + 1)) (by positivity)
  refine this.trans ?_
  have : 2 * δ / (Fintype.card I + 1) * Fintype.card I / 2 ≤ δ := by
    rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

lemma sqrt_herm (X : Matrix I I ℂ) : (cfc Real.sqrt X)ᴴ = cfc Real.sqrt X :=
  (cfc_predicate Real.sqrt X : IsSelfAdjoint _)

lemma sqrt_sq {X : Matrix I I ℂ} (hX : X.PosSemidef) : cfc Real.sqrt X * cfc Real.sqrt X = X := by
  have hs : IsSelfAdjoint X := hX.1.isSelfAdjoint
  rw [← cfc_mul _ _ _ (fin _ _) (fin _ _)]
  conv_rhs => rw [← cfc_id' ℝ X hs]
  refine cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hX.nonneg hx)

end CFCBasics
namespace Nuclear
open Polynomial
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
lemma tr_pow_swap (X : Matrix m n ℂ) (k : ℕ) :
    ((Xᴴ * X) ^ (k + 1)).trace = ((X * Xᴴ) ^ (k + 1)).trace := by
  have h : ∀ k : ℕ, (Xᴴ * X) ^ (k + 1) = Xᴴ * (X * Xᴴ) ^ k * X := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']

lemma tr_aeval_swap (X : Matrix m n ℂ) (p : ℝ[X]) (hp : p.coeff 0 = 0) :
    (aeval (Xᴴ * X) p).trace = (aeval (X * Xᴴ) p).trace := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [hp]
  · rw [tr_pow_swap]

theorem tr_cfc_swap (X : Matrix m n ℂ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f (Xᴴ * X)).trace = (cfc f (X * Xᴴ)).trace := by
  set A := Xᴴ * X
  set B := X * Xᴴ
  have hA : IsSelfAdjoint A := (Matrix.posSemidef_conjTranspose_mul_self X).1.isSelfAdjoint
  have hB : IsSelfAdjoint B := (Matrix.posSemidef_self_mul_conjTranspose X).1.isSelfAdjoint
  have fA : (spectrum ℝ A).Finite := A.finite_real_spectrum
  have fB : (spectrum ℝ B).Finite := B.finite_real_spectrum
  set s : Finset ℝ := {0} ∪ fA.toFinset ∪ fB.toFinset
  set p := Lagrange.interpolate s (fun x : ℝ => x) f
  have hp : ∀ x ∈ s, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := fun x : ℝ => x) f (fun a _ b _ h => h) hx
  have h1 : cfc f A = cfc (fun x => p.eval x) A :=
    cfc_congr fun x hx => (hp x (by simp [s, fA.mem_toFinset.2 hx])).symm
  have h2 : cfc f B = cfc (fun x => p.eval x) B :=
    cfc_congr fun x hx => (hp x (by simp [s, fB.mem_toFinset.2 hx])).symm
  rw [h1, h2, cfc_polynomial p A hA, cfc_polynomial p B hB]
  refine tr_aeval_swap X p ?_
  rw [Polynomial.coeff_zero_eq_eval_zero, hp 0 (by simp [s]), hf]

section Polar
variable {R : Type*} [Fintype R] [DecidableEq R]
lemma dot_self (Y : Matrix R R ℂ) (v : R → ℂ) :
    star (Y *ᵥ v) ⬝ᵥ (Y *ᵥ v) = star v ⬝ᵥ ((Yᴴ * Y) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

lemma norm_sq_eq (x : EuclideanSpace ℂ R) : ((‖x‖ ^ 2 : ℝ) : ℂ) = star (x.ofLp) ⬝ᵥ x.ofLp := by
  rw [Complex.ofReal_pow, show ((‖x‖ : ℂ)) ^ 2 = inner ℂ x x from
    (inner_self_eq_norm_sq_to_K x).symm, PiLp.inner_apply]
  simp [dotProduct, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

/-- Polar decomposition: `Y = W |Y|` with `W` unitary. -/
theorem polar (Y : Matrix R R ℂ) :
    ∃ W : Matrix.unitaryGroup R ℂ, (W : Matrix R R ℂ) * cfc Real.sqrt (Yᴴ * Y) = Y := by
  set G := Yᴴ * Y
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self Y
  set A := cfc Real.sqrt G
  set Ap := cfc (fun x => (Real.sqrt x)⁻¹) G
  set P := cfc (fun x => Real.sqrt x * (Real.sqrt x)⁻¹) G
  have hAh : Aᴴ = A := CFCBasics.sqrt_herm G
  have hAA : A * A = G := CFCBasics.sqrt_sq hG
  have hApA : Ap * A = P := by
    rw [← cfc_mul _ _ _ (CFCBasics.fin _ _) (CFCBasics.fin _ _)]
    exact cfc_congr fun x _ => mul_comm _ _
  have hA1P : A * (1 - P) = 0 := by
    rw [← cfc_one ℝ G, ← cfc_sub _ _ _ (CFCBasics.fin _ _) (CFCBasics.fin _ _),
      ← cfc_mul _ _ _ (CFCBasics.fin _ _) (CFCBasics.fin _ _)]
    rw [show (0 : Matrix R R ℂ) = cfc (fun _ : ℝ => (0 : ℝ)) G by simp]
    refine cfc_congr fun x _ => ?_
    by_cases h : Real.sqrt x = 0
    · simp [h]
    · simp [mul_inv_cancel₀ h]
  have hY1P : Y * (1 - P) = 0 := by
    have : (Y * (1 - P))ᴴ * (Y * (1 - P)) = 0 := by
      have e : (Y * (1 - P))ᴴ * (Y * (1 - P)) = (A * (1 - P))ᴴ * (A * (1 - P)) := by
        simp only [conjTranspose_mul, hAh]
        rw [show (1 - P)ᴴ * Yᴴ * (Y * (1 - P)) = (1 - P)ᴴ * G * (1 - P) by
            simp only [G, Matrix.mul_assoc],
          ← hAA]
        simp only [Matrix.mul_assoc]
      rw [e, hA1P, Matrix.mul_zero]
    exact Matrix.conjTranspose_mul_self_eq_zero.mp this
  set M := Y * Ap
  have hMA : M * A = Y := by
    rw [Matrix.mul_assoc, hApA]
    have := hY1P
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
    exact this.symm
  -- isometry on the range of A
  have hnorm : ∀ v : R → ℂ, ‖(WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)‖ =
      ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)‖ := by
    intro v
    have h1 := norm_sq_eq (WithLp.toLp 2 (Y *ᵥ v) : EuclideanSpace ℂ R)
    have h2 := norm_sq_eq (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R)
    simp only [WithLp.ofLp_toLp] at h1 h2
    rw [dot_self] at h1
    rw [dot_self, hAh, hAA] at h2
    rw [← h2] at h1
    have := Complex.ofReal_injective h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  set TA := Matrix.toEuclideanLin A
  set S := LinearMap.range TA
  let L : S →ₗᵢ[ℂ] EuclideanSpace ℂ R :=
    { toLinearMap := (Matrix.toEuclideanLin M).domRestrict S
      norm_map' := by
        rintro ⟨s, v, rfl⟩
        simp only [LinearMap.domRestrict_apply, TA, Matrix.toEuclideanLin_apply,
          WithLp.ofLp_toLp, Matrix.mulVec_mulVec, hMA, Submodule.coe_norm]
        exact hnorm _ }
  set W := L.extend
  set Wm := Matrix.toEuclideanLin.symm W.toLinearMap
  have hW : ∀ x, Matrix.toEuclideanLin Wm x = W x := by
    intro x; simp [Wm]
  have hWv : ∀ u : R → ℂ, Wm *ᵥ u = (W (WithLp.toLp 2 u)).ofLp := by
    intro u; rw [← hW]; simp
  have hWA : Wm * A = Y := by
    refine Matrix.ext_iff_mulVec.2 fun v => ?_
    rw [← Matrix.mulVec_mulVec, hWv]
    have hx : (WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ R) ∈ S := ⟨WithLp.toLp 2 v, by simp [TA]⟩
    have := L.extend_apply ⟨_, hx⟩
    simp only at this
    rw [this]
    simp [L, Matrix.mulVec_mulVec, hMA]
  have hU : Wm ∈ Matrix.unitaryGroup R ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have := W.inner_map_map (EuclideanSpace.single i (1 : ℂ)) (EuclideanSpace.single j 1)
    have hc : ∀ j : R, (W (EuclideanSpace.single j (1 : ℂ))).ofLp = Wm.col j := by
      intro j; rw [← Matrix.mulVec_single_one, hWv]; rfl
    rw [EuclideanSpace.inner_single_left, PiLp.inner_apply] at this
    simp only [hc] at this
    simp only [star_eq_conjTranspose, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply]
    convert this using 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Matrix.col_apply, RCLike.inner_apply]
      exact mul_comm _ _
    · simp [EuclideanSpace.single_apply, eq_comm]
  exact ⟨⟨Wm, hU⟩, hWA⟩
lemma psd_tr {X : Matrix R R ℂ} (h : X.PosSemidef) : X.trace = ((X.trace.re : ℝ) : ℂ) := by
  have := h.trace_nonneg
  rw [Complex.nonneg_iff] at this
  exact Complex.ext (by simp) (by simp [← this.2])

/-- `|Tr (Z V)| ≤ Tr √(Z Z†)` for unitary `V`. -/
lemma abs_tr_le (Z V : Matrix R R ℂ) (hV : V * Vᴴ = 1) :
    ‖(Z * V).trace‖ ≤ (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  set t := (Z * V).trace
  by_cases ht : t = 0
  · rw [ht, norm_zero]
    exact CFCBasics.psd_re (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) :
      0 ≤ cfc Real.sqrt (Z * Zᴴ)).posSemidef
  set c : ℂ := star t / (‖t‖ : ℂ)
  have hn : (‖t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ht
  have hc : c * star c = 1 := by
    simp only [c, star_div₀, star_star, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    rw [div_mul_div_comm, Complex.conj_mul', ← pow_two]
    exact div_self (pow_ne_zero 2 hn)
  have h := CFCBasics.re_tr_le (c • (Z * V))
  have e1 : (c • (Z * V)) * (c • (Z * V))ᴴ = Z * Zᴴ := by
    rw [conjTranspose_smul, smul_mul_smul_comm, hc, one_smul, conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc V, hV, Matrix.one_mul]
  have e2 : (c • (Z * V)).trace.re = ‖t‖ := by
    rw [Matrix.trace_smul, smul_eq_mul]
    simp only [c, Complex.star_def]
    rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [pow_two, mul_div_assoc, div_self hn, mul_one]
    simp only [Complex.ofReal_re]; rfl
  rw [e1, e2] at h
  exact h

lemma tr_attain (Z : Matrix R R ℂ) :
    ∃ V : Matrix.unitaryGroup R ℂ, ‖(Z * (V : Matrix R R ℂ)).trace‖ =
      (cfc Real.sqrt (Z * Zᴴ)).trace.re := by
  obtain ⟨W, hW⟩ := polar Zᴴ
  rw [conjTranspose_conjTranspose] at hW
  have hZ : Z = cfc Real.sqrt (Z * Zᴴ) * (W : Matrix R R ℂ)ᴴ := by
    have := congrArg conjTranspose hW
    rw [conjTranspose_conjTranspose, conjTranspose_mul, CFCBasics.sqrt_herm] at this
    exact this.symm
  refine ⟨W, ?_⟩
  have hWW : (W : Matrix R R ℂ)ᴴ * W = 1 := by
    have := W.2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  nth_rewrite 1 [hZ]
  rw [Matrix.mul_assoc, hWW, Matrix.mul_one]
  have hp : (cfc Real.sqrt (Z * Zᴴ)).PosSemidef :=
    (cfc_nonneg (fun x _ => Real.sqrt_nonneg x) : 0 ≤ cfc Real.sqrt (Z * Zᴴ)).posSemidef
  rw [psd_tr hp, Complex.norm_real, Real.norm_of_nonneg (CFCBasics.psd_re hp), Complex.ofReal_re]

end Polar
end Nuclear
end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetNuclearNorm -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma sqrt_eq_cfc (A : Matrix α α ℂ) (hA:A.PosSemidef) :
    CFC.sqrt A=cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA.nonneg,cfcₙ_eq_cfc]

/-- The public trace norm agrees with either rectangular Gram expression. -/
lemma traceNorm_eq_left (A : Matrix α β ℂ) :
    WildeQIT.traceNorm A=(cfc Real.sqrt (A*Aᴴ)).trace.re := by
  rw [WildeQIT.traceNorm,sqrt_eq_cfc _ (Matrix.posSemidef_conjTranspose_mul_self A),
    Nuclear.tr_cfc_swap A _ Real.sqrt_zero]

lemma traceNorm_nonneg (A : Matrix α β ℂ) : 0 ≤ WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left]
  exact CFCBasics.psd_re (cfc_nonneg (fun _ _=>Real.sqrt_nonneg _) :
    0 ≤ cfc Real.sqrt (A*Aᴴ)).posSemidef

lemma traceNorm_zero : WildeQIT.traceNorm (0:Matrix α β ℂ)=0 := by
  simp [WildeQIT.traceNorm]

lemma traceNorm_dual (A : Matrix α α ℂ) (U : Matrix.unitaryGroup α ℂ) :
    ‖(A*(U:Matrix α α ℂ)).trace‖ ≤ WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left]
  exact Nuclear.abs_tr_le A U (by exact Unitary.coe_mul_star_self U)

lemma traceNorm_attain (A : Matrix α α ℂ) :
    ∃ U : Matrix.unitaryGroup α ℂ,‖(A*(U:Matrix α α ℂ)).trace‖=WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left]
  exact Nuclear.tr_attain A

lemma traceNorm_add_le_square (A B : Matrix α α ℂ) :
    WildeQIT.traceNorm (A+B) ≤ WildeQIT.traceNorm A+WildeQIT.traceNorm B := by
  obtain ⟨U,hU⟩:=traceNorm_attain (A+B)
  rw [← hU,add_mul,Matrix.trace_add]
  exact (norm_add_le _ _).trans (add_le_add (traceNorm_dual A U) (traceNorm_dual B U))

lemma traceNorm_smul_square (c : ℂ) (A : Matrix α α ℂ) :
    WildeQIT.traceNorm (c • A)=‖c‖*WildeQIT.traceNorm A := by
  apply le_antisymm
  · obtain ⟨U,hU⟩:=traceNorm_attain (c • A)
    rw [← hU,Matrix.smul_mul,Matrix.trace_smul,norm_smul]
    exact mul_le_mul_of_nonneg_left (traceNorm_dual A U) (norm_nonneg _)
  · obtain ⟨U,hU⟩:=traceNorm_attain A
    have hh:=traceNorm_dual (c • A) U
    rwa [Matrix.smul_mul,Matrix.trace_smul,norm_smul,hU] at hh

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetNuclearBlocks -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma fromBlocks_diagonal_posSemidef (A : Matrix α α ℂ) (D : Matrix β β ℂ)
    (hA:A.PosSemidef) (hD:D.PosSemidef) : (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  let S : Matrix (α⊕β) (α⊕β) ℂ := Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt D)
  have hs:Sᴴ=S := by
    simp only [S,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero]
    have ha:(CFC.sqrt A)ᴴ=CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
    have hd:(CFC.sqrt D)ᴴ=CFC.sqrt D := (CFC.sqrt_nonneg D).isSelfAdjoint.star_eq
    rw [ha,hd]
  have hss:S*S=Matrix.fromBlocks A 0 0 D := by
    simp only [S,Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,
      CFC.sqrt_mul_sqrt_self A hA.nonneg,CFC.sqrt_mul_sqrt_self D hD.nonneg]
  have hp:=Matrix.posSemidef_conjTranspose_mul_self S
  rw [hs,hss] at hp
  exact hp

lemma sqrt_fromBlocks_diagonal (A : Matrix α α ℂ) (D : Matrix β β ℂ)
    (hA:A.PosSemidef) (hD:D.PosSemidef) :
    CFC.sqrt (Matrix.fromBlocks A 0 0 D)=Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt D) := by
  apply (CFC.sqrt_eq_iff _ _ (fromBlocks_diagonal_posSemidef A D hA hD).nonneg
    (fromBlocks_diagonal_posSemidef _ _ (CFC.sqrt_nonneg A).posSemidef (CFC.sqrt_nonneg D).posSemidef).nonneg).mpr
  simp only [Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,
    CFC.sqrt_mul_sqrt_self A hA.nonneg,CFC.sqrt_mul_sqrt_self D hD.nonneg]

lemma trace_fromBlocks_diagonal (A : Matrix α α ℂ) (D : Matrix β β ℂ) :
    (Matrix.fromBlocks A 0 0 D).trace=A.trace+D.trace := by
  simp [Matrix.trace,Fintype.sum_sum_type,Matrix.diag]

def hermitianDilation (A : Matrix α β ℂ) : Matrix (α⊕β) (α⊕β) ℂ :=
  Matrix.fromBlocks 0 A Aᴴ 0

lemma hermitianDilation_hermitian (A : Matrix α β ℂ) : (hermitianDilation A)ᴴ=hermitianDilation A := by
  simp [hermitianDilation,Matrix.fromBlocks_conjTranspose]

lemma hermitianDilation_gram (A : Matrix α β ℂ) :
    (hermitianDilation A)ᴴ*hermitianDilation A=Matrix.fromBlocks (A*Aᴴ) 0 0 (Aᴴ*A) := by
  rw [hermitianDilation_hermitian]
  simp [hermitianDilation,Matrix.fromBlocks_multiply]

/-- An off-diagonal Hermitian dilation has twice the exact public nuclear norm. -/
lemma traceNorm_hermitianDilation (A : Matrix α β ℂ) :
    WildeQIT.traceNorm (hermitianDilation A)=2*WildeQIT.traceNorm A := by
  rw [WildeQIT.traceNorm,hermitianDilation_gram,
    sqrt_fromBlocks_diagonal _ _ (Matrix.posSemidef_self_mul_conjTranspose A)
      (Matrix.posSemidef_conjTranspose_mul_self A),trace_fromBlocks_diagonal,Complex.add_re]
  have he:(CFC.sqrt (A*Aᴴ)).trace.re=WildeQIT.traceNorm A := by
    rw [sqrt_eq_cfc _ (Matrix.posSemidef_self_mul_conjTranspose A),traceNorm_eq_left]
  rw [he]
  change WildeQIT.traceNorm A+WildeQIT.traceNorm A=2*WildeQIT.traceNorm A
  ring

lemma hermitianDilation_add (A B : Matrix α β ℂ) :
    hermitianDilation (A+B)=hermitianDilation A+hermitianDilation B := by
  simp [hermitianDilation,Matrix.fromBlocks_add]

/-- The triangle inequality also holds for the rectangular trace norm. -/
theorem traceNorm_add_le (A B : Matrix α β ℂ) :
    WildeQIT.traceNorm (A+B) ≤ WildeQIT.traceNorm A+WildeQIT.traceNorm B := by
  have hh:=traceNorm_add_le_square (hermitianDilation A) (hermitianDilation B)
  rw [← hermitianDilation_add,traceNorm_hermitianDilation,traceNorm_hermitianDilation,
    traceNorm_hermitianDilation] at hh
  linarith

theorem traceNorm_sum_le {ι : Type} (S : Finset ι) (A : ι→Matrix α β ℂ) :
    WildeQIT.traceNorm (∑i∈S,A i) ≤ ∑i∈S,WildeQIT.traceNorm (A i) := by
  induction S using Finset.cons_induction with
  | empty => simp [traceNorm_zero]
  | @cons i S hi ih =>
    rw [Finset.sum_cons hi,Finset.sum_cons hi]
    exact (traceNorm_add_le _ _).trans (add_le_add (le_refl _) ih)

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetHilbertSchmidt -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

def entryVector (A : Matrix α β ℂ) : EuclideanSpace ℂ (α×β) :=
  WithLp.toLp 2 (fun p=>A p.1 p.2)

def hsNorm (A : Matrix α β ℂ) : ℝ := Real.sqrt (Aᴴ*A).trace.re

lemma trace_gram_eq_inner (A B : Matrix α β ℂ) :
    (Aᴴ*B).trace=inner ℂ (entryVector A) (entryVector B) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    entryVector,PiLp.inner_apply,WithLp.ofLp_toLp,RCLike.inner_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact mul_comm _ _

lemma hsNorm_eq_norm (A : Matrix α β ℂ) : hsNorm A=‖entryVector A‖ := by
  rw [hsNorm,trace_gram_eq_inner,inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal,← Complex.ofReal_pow,Complex.ofReal_re]
  exact Real.sqrt_sq (norm_nonneg _)

lemma hsNorm_nonneg (A : Matrix α β ℂ) : 0 ≤ hsNorm A := Real.sqrt_nonneg _

lemma hs_trace_cauchy (A B : Matrix α β ℂ) :
    ‖(Aᴴ*B).trace‖ ≤ hsNorm A*hsNorm B := by
  rw [trace_gram_eq_inner,hsNorm_eq_norm,hsNorm_eq_norm]
  exact norm_inner_le_norm _ _

lemma hsNorm_conjTranspose (A : Matrix α β ℂ) : hsNorm Aᴴ=hsNorm A := by
  rw [hsNorm,hsNorm,Matrix.conjTranspose_conjTranspose,Matrix.trace_mul_comm]

lemma hsNorm_mul_unitary (A : Matrix α β ℂ) (U : Matrix.unitaryGroup β ℂ) :
    hsNorm (A*(U:Matrix β β ℂ))=hsNorm A := by
  unfold hsNorm
  congr 1
  have he:((A*(U:Matrix β β ℂ))ᴴ*(A*(U:Matrix β β ℂ))).trace=(Aᴴ*A).trace := by
    rw [Matrix.conjTranspose_mul]
    rw [show (U:Matrix β β ℂ)ᴴ*Aᴴ*(A*(U:Matrix β β ℂ))=
      (U:Matrix β β ℂ)ᴴ*(Aᴴ*A)*(U:Matrix β β ℂ) by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_cycle]
    have hu:(U:Matrix β β ℂ)*(U:Matrix β β ℂ)ᴴ=1 := Unitary.coe_mul_star_self U
    rw [hu,Matrix.one_mul]
  rw [he]

lemma traceNorm_mul_le_hs_square (A B : Matrix α α ℂ) :
    WildeQIT.traceNorm (A*B) ≤ hsNorm A*hsNorm B := by
  obtain ⟨U,hU⟩:=traceNorm_attain (A*B)
  have hh:=hs_trace_cauchy Aᴴ (B*(U:Matrix α α ℂ))
  rw [Matrix.conjTranspose_conjTranspose,← Matrix.mul_assoc,hU,
    hsNorm_conjTranspose,hsNorm_mul_unitary] at hh
  exact hh

/-- Schatten 2–2→1 Hölder, with arbitrary finite rectangular dimensions. -/
theorem traceNorm_mul_le_hs (A : Matrix α β ℂ) (B : Matrix β γ ℂ) :
    WildeQIT.traceNorm (A*B) ≤ hsNorm A*hsNorm B := by
  let S : Matrix β β ℂ := CFC.sqrt (Aᴴ*A)
  let T : Matrix β β ℂ := CFC.sqrt (B*Bᴴ)
  have hS:Sᴴ=S := (CFC.sqrt_nonneg (Aᴴ*A)).isSelfAdjoint.star_eq
  have hT:Tᴴ=T := (CFC.sqrt_nonneg (B*Bᴴ)).isSelfAdjoint.star_eq
  have hSS:S*S=Aᴴ*A := CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have hTT:T*T=B*Bᴴ := CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_self_mul_conjTranspose B).nonneg
  have he1:WildeQIT.traceNorm (A*B)=WildeQIT.traceNorm (S*B) := by
    have hg:(A*B)ᴴ*(A*B)=(S*B)ᴴ*(S*B) := by
      simp only [Matrix.conjTranspose_mul,hS]
      simp only [Matrix.mul_assoc,← Matrix.mul_assoc S S,hSS]
    simp only [WildeQIT.traceNorm,hg]
  have he2:WildeQIT.traceNorm (S*B)=WildeQIT.traceNorm (S*T) := by
    have hg:(S*B)*(S*B)ᴴ=(S*T)*(S*T)ᴴ := by
      simp only [Matrix.conjTranspose_mul,hS,hT]
      simp only [Matrix.mul_assoc,← Matrix.mul_assoc T T,hTT]
    rw [traceNorm_eq_left,traceNorm_eq_left,hg]
  have hnS:hsNorm S=hsNorm A := by rw [hsNorm,hS,hSS];rfl
  have hnT:hsNorm T=hsNorm B := by
    rw [hsNorm,hT,hTT,Matrix.trace_mul_comm]
    rfl
  rw [he1,he2]
  exact (traceNorm_mul_le_hs_square S T).trans_eq (by rw [hnS,hnT])

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetNuclearOrder -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

lemma sqrt_smul_sq (r : ℝ) (hr:0 ≤ r) (A : Matrix α α ℂ) (hA:A.PosSemidef) :
    CFC.sqrt ((r^2:ℝ) • A)=r • CFC.sqrt A := by
  apply (CFC.sqrt_eq_iff _ _ (hA.smul (sq_nonneg r)).nonneg
    ((CFC.sqrt_nonneg A).posSemidef.smul hr).nonneg).mpr
  rw [smul_mul_smul_comm,CFC.sqrt_mul_sqrt_self A hA.nonneg,pow_two]

lemma traceNorm_of_posSemidef (A : Matrix α α ℂ) (hA:A.PosSemidef) :
    WildeQIT.traceNorm A=A.trace.re := by
  rw [WildeQIT.traceNorm,hA.isHermitian.eq,CFC.sqrt_mul_self A hA.nonneg]

lemma traceNorm_conjTranspose (A : Matrix α β ℂ) : WildeQIT.traceNorm Aᴴ=WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left,Matrix.conjTranspose_conjTranspose,WildeQIT.traceNorm,
    sqrt_eq_cfc _ (Matrix.posSemidef_conjTranspose_mul_self A)]

lemma traceNorm_mul_coisometry (A : Matrix α β ℂ) (U : Matrix β γ ℂ) (hU:U*Uᴴ=1) :
    WildeQIT.traceNorm (A*U)=WildeQIT.traceNorm A := by
  rw [traceNorm_eq_left,traceNorm_eq_left,Matrix.conjTranspose_mul]
  rw [show A*U*(Uᴴ*Aᴴ)=A*(U*Uᴴ)*Aᴴ by simp only [Matrix.mul_assoc],hU,Matrix.mul_one]

open scoped Matrix.Norms.L2Operator in
/-- Multiplication by an operator bounded by r contracts nuclear norm by r;
the hypothesis is expressed by the actual finite positive-semidefinite order. -/
theorem traceNorm_mul_left_le (A : Matrix α β ℂ) (B : Matrix β γ ℂ) (r : ℝ) (hr:0 ≤ r)
    (hA:((r^2:ℝ) • (1:Matrix β β ℂ)-Aᴴ*A).PosSemidef) :
    WildeQIT.traceNorm (A*B) ≤ r*WildeQIT.traceNorm B := by
  have hconj:=hA.mul_mul_conjTranspose_same Bᴴ
  rw [Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one] at hconj
  have he:(A*B)ᴴ*(A*B)=Bᴴ*(Aᴴ*A)*B := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  have hord:(A*B)ᴴ*(A*B) ≤ (r^2:ℝ) • (Bᴴ*B) := by
    rw [Matrix.le_iff,he]
    exact hconj
  have hs:=CFC.sqrt_le_sqrt _ _ hord
  have ht:=CFCBasics.psd_re (Matrix.le_iff.mp hs)
  rw [Matrix.trace_sub,Complex.sub_re] at ht
  rw [sqrt_smul_sq r hr _ (Matrix.posSemidef_conjTranspose_mul_self B),Matrix.trace_smul,
    Complex.real_smul] at ht
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at ht
  change 0 ≤ r*WildeQIT.traceNorm B-WildeQIT.traceNorm (A*B) at ht
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetFidelityFactors -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-- Root fidelity, expressed by the exact public CFC-based trace norm. -/
def rootFidelity (ρ σ : Matrix α α ℂ) : ℝ :=
  WildeQIT.traceNorm (CFC.sqrt ρ*CFC.sqrt σ)

lemma rootFidelity_nonneg (ρ σ : Matrix α α ℂ) : 0 ≤ rootFidelity ρ σ := traceNorm_nonneg _

lemma rootFidelity_symm (ρ σ : Matrix α α ℂ) : rootFidelity ρ σ=rootFidelity σ ρ := by
  have hρ:(CFC.sqrt ρ)ᴴ=CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq
  have hσ:(CFC.sqrt σ)ᴴ=CFC.sqrt σ := (CFC.sqrt_nonneg σ).isSelfAdjoint.star_eq
  unfold rootFidelity
  rw [← traceNorm_conjTranspose (CFC.sqrt ρ*CFC.sqrt σ),Matrix.conjTranspose_mul,hρ,hσ]

lemma hsNorm_sqrt (ρ : Matrix α α ℂ) (hρ:ρ.PosSemidef) : hsNorm (CFC.sqrt ρ)=Real.sqrt ρ.trace.re := by
  have hh:(CFC.sqrt ρ)ᴴ=CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq
  rw [hsNorm,hh,CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]

lemma rootFidelity_trace_bound (ρ σ : Matrix α α ℂ) (hρ:ρ.PosSemidef) (hσ:σ.PosSemidef) :
    rootFidelity ρ σ ≤ Real.sqrt ρ.trace.re*Real.sqrt σ.trace.re := by
  unfold rootFidelity
  exact (traceNorm_mul_le_hs _ _).trans_eq (by rw [hsNorm_sqrt ρ hρ,hsNorm_sqrt σ hσ])

lemma traceNorm_swap_grams (A : Matrix α β ℂ) (B : Matrix γ α ℂ)
    (h:A*Aᴴ=Bᴴ*B) : WildeQIT.traceNorm A=WildeQIT.traceNorm B := by
  rw [traceNorm_eq_left,WildeQIT.traceNorm,sqrt_eq_cfc _ (Matrix.posSemidef_conjTranspose_mul_self B),h]

/-- Uhlmann's factor identity, allowing subnormalized and rank-deficient
matrices and arbitrary finite purification dimension. -/
theorem rootFidelity_factors (Ψ Φ : Matrix α β ℂ) :
    rootFidelity (Ψ*Ψᴴ) (Φ*Φᴴ)=WildeQIT.traceNorm (Ψᴴ*Φ) := by
  let S := CFC.sqrt (Ψ*Ψᴴ)
  let T := CFC.sqrt (Φ*Φᴴ)
  have hS:Sᴴ=S := (CFC.sqrt_nonneg (Ψ*Ψᴴ)).isSelfAdjoint.star_eq
  have hT:Tᴴ=T := (CFC.sqrt_nonneg (Φ*Φᴴ)).isSelfAdjoint.star_eq
  have hSS:S*S=Ψ*Ψᴴ := CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_self_mul_conjTranspose Ψ).nonneg
  have hTT:T*T=Φ*Φᴴ := CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_self_mul_conjTranspose Φ).nonneg
  change WildeQIT.traceNorm (S*T)= _
  calc
    _ = WildeQIT.traceNorm (Φᴴ*S) := traceNorm_swap_grams _ _ (by
      simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hS,hT]
      simp only [Matrix.mul_assoc,← Matrix.mul_assoc T T,hTT])
    _ = WildeQIT.traceNorm (Ψᴴ*Φ) := traceNorm_swap_grams _ _ (by
      simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hS]
      simp only [Matrix.mul_assoc,← Matrix.mul_assoc S S,hSS])

/-- Changing one purification factor changes fidelity to a normalized target
by at most its Hilbert–Schmidt distance. -/
theorem rootFidelity_factor_lipschitz (T A B : Matrix α β ℂ) (hT:(T*Tᴴ).trace=1) :
    rootFidelity (T*Tᴴ) (A*Aᴴ)-hsNorm (A-B) ≤ rootFidelity (T*Tᴴ) (B*Bᴴ) := by
  rw [rootFidelity_factors,rootFidelity_factors]
  have hn:hsNorm Tᴴ=1 := by
    rw [hsNorm,Matrix.conjTranspose_conjTranspose,hT]
    norm_num
  have hd:=traceNorm_mul_le_hs Tᴴ (A-B)
  rw [hn,one_mul] at hd
  have he:Tᴴ*A=Tᴴ*B+Tᴴ*(A-B) := by rw [Matrix.mul_sub];abel
  have ht:=traceNorm_add_le (Tᴴ*B) (Tᴴ*(A-B))
  rw [← he] at ht
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetFidelityClippingScalar -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α : Type} [Fintype α] [DecidableEq α]

lemma sqrt_smul_nonneg (r : ℝ) (hr:0 ≤ r) (A : Matrix α α ℂ) (hA:A.PosSemidef) :
    CFC.sqrt (r • A)=Real.sqrt r • CFC.sqrt A := by
  have hh:=sqrt_smul_sq (Real.sqrt r) (Real.sqrt_nonneg _) A hA
  simpa only [Real.sq_sqrt hr] using hh

lemma traceNorm_real_smul_square (r : ℝ) (hr:0 ≤ r) (A : Matrix α α ℂ) :
    WildeQIT.traceNorm (r • A)=r*WildeQIT.traceNorm A := by
  have he:r • A=(r:ℂ) • A := by
    ext i j
    exact Complex.real_smul
  rw [he,traceNorm_smul_square,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]

lemma rootFidelity_smul_right (A B : Matrix α α ℂ) (hB:B.PosSemidef) (r : ℝ) (hr:0 ≤ r) :
    rootFidelity A (r • B)=Real.sqrt r*rootFidelity A B := by
  rw [rootFidelity,sqrt_smul_nonneg r hr B hB,Matrix.mul_smul,
    traceNorm_real_smul_square _ (Real.sqrt_nonneg _)]
  rfl

def clipCoefficient (p q : ℝ) : ℝ := if p<q then p/q else 1

lemma clipCoefficient_nonneg (p q : ℝ) (hp:0<p) (hq:0 ≤ q) : 0 ≤ clipCoefficient p q := by
  unfold clipCoefficient
  split_ifs <;> positivity

lemma clipCoefficient_le_one (p q : ℝ) (hp:0<p) (hq:0 ≤ q) : clipCoefficient p q ≤ 1 := by
  unfold clipCoefficient
  split_ifs with h
  · exact (div_le_one (by linarith : 0<q)).mpr (le_of_lt h)
  · exact le_rfl

lemma clipCoefficient_trace_le (p q : ℝ) (hp:0<p) (hq:0 ≤ q) : clipCoefficient p q*q ≤ p := by
  unfold clipCoefficient
  split_ifs with h
  · rw [div_mul_cancel₀ _ (by linarith : q ≠ 0)]
  · simp only [one_mul]
    linarith

/-- Exact scalar estimate behind the linear delta/2 clipping loss. -/
lemma clipping_loss (p q F : ℝ) (hp:0<p) (hq:0 ≤ q)
    (hF:F ≤ Real.sqrt p*Real.sqrt q) :
    F-Real.sqrt (clipCoefficient p q)*F ≤ max (q-p) 0/2 := by
  by_cases hpq:p<q
  · have hq0:0<q := by linarith
    have hc:clipCoefficient p q=p/q := if_pos hpq
    rw [hc,Real.sqrt_div hp.le]
    have hs:0<Real.sqrt q := Real.sqrt_pos.mpr hq0
    have hsp:=Real.mul_self_sqrt hp.le
    have hsq:=Real.mul_self_sqrt hq
    have hle:Real.sqrt p ≤ Real.sqrt q := Real.sqrt_le_sqrt hpq.le
    have hfactor:0 ≤ 1-Real.sqrt p/Real.sqrt q := by
      exact sub_nonneg.mpr ((div_le_one hs).mpr hle)
    have hh:=mul_le_mul_of_nonneg_left hF hfactor
    have he:(1-Real.sqrt p/Real.sqrt q)*(Real.sqrt p*Real.sqrt q)=Real.sqrt p*Real.sqrt q-p := by
      field_simp
      nlinarith
    rw [he] at hh
    rw [max_eq_left (by linarith : 0 ≤ q-p)]
    nlinarith [sq_nonneg (Real.sqrt q-Real.sqrt p)]
  · have hc:clipCoefficient p q=1 := if_neg hpq
    rw [hc,Real.sqrt_one,one_mul]
    have hh:q-p ≤ 0 := by linarith
    rw [max_eq_right hh]
    simp

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetBlockMatrices -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {ι α β γ : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

def blockMatrix (A : ι→Matrix α β ℂ) : Matrix (ι×α) (ι×β) ℂ :=
  fun x y=>if x.1=y.1 then A x.1 x.2 y.2 else 0

lemma blockMatrix_star (A : ι→Matrix α β ℂ) :
    (blockMatrix A)ᴴ=blockMatrix (fun i=>(A i)ᴴ) := by
  ext x y
  by_cases h:x.1=y.1
  · simp [blockMatrix,Matrix.conjTranspose_apply,h]
  · simp [blockMatrix,Matrix.conjTranspose_apply,h,Ne.symm h]

lemma blockMatrix_mul (A : ι→Matrix α β ℂ) (B : ι→Matrix β γ ℂ) :
    blockMatrix A*blockMatrix B=blockMatrix (fun i=>A i*B i) := by
  ext x y
  by_cases h:x.1=y.1
  · simp [blockMatrix,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,mul_ite,h]
  · simp [blockMatrix,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul,mul_ite,h]

lemma blockMatrix_trace (A : ι→Matrix α α ℂ) : (blockMatrix A).trace=∑i,(A i).trace := by
  simp [blockMatrix,Matrix.trace,Matrix.diag,Fintype.sum_prod_type]

lemma blockMatrix_posSemidef (A : ι→Matrix α α ℂ) (hA:∀i,(A i).PosSemidef) :
    (blockMatrix A).PosSemidef := by
  let S := blockMatrix (fun i=>CFC.sqrt (A i))
  have he:Sᴴ*S=blockMatrix A := by
    rw [blockMatrix_star,blockMatrix_mul]
    congr 1
    funext i
    have hs:(CFC.sqrt (A i))ᴴ=CFC.sqrt (A i) := (CFC.sqrt_nonneg (A i)).isSelfAdjoint.star_eq
    rw [hs,CFC.sqrt_mul_sqrt_self _ (hA i).nonneg]
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self S

lemma blockMatrix_sqrt (A : ι→Matrix α α ℂ) (hA:∀i,(A i).PosSemidef) :
    CFC.sqrt (blockMatrix A)=blockMatrix (fun i=>CFC.sqrt (A i)) := by
  apply (CFC.sqrt_eq_iff _ _ (blockMatrix_posSemidef A hA).nonneg
    (blockMatrix_posSemidef _ (fun i=>(CFC.sqrt_nonneg (A i)).posSemidef)).nonneg).mpr
  rw [blockMatrix_mul]
  congr 1
  funext i
  exact CFC.sqrt_mul_sqrt_self _ (hA i).nonneg

lemma blockMatrix_traceNorm (A : ι→Matrix α β ℂ) :
    WildeQIT.traceNorm (blockMatrix A)=∑i,WildeQIT.traceNorm (A i) := by
  rw [WildeQIT.traceNorm,blockMatrix_star,blockMatrix_mul,
    blockMatrix_sqrt _ (fun i=>Matrix.posSemidef_conjTranspose_mul_self (A i)),blockMatrix_trace]
  rw [Complex.re_sum]
  rfl

/-- Root fidelity is additive on literal orthogonal classical-label blocks. -/
theorem rootFidelity_blockMatrix (A B : ι→Matrix α α ℂ)
    (hA:∀i,(A i).PosSemidef) (hB:∀i,(B i).PosSemidef) :
    rootFidelity (blockMatrix A) (blockMatrix B)=∑i,rootFidelity (A i) (B i) := by
  rw [rootFidelity,blockMatrix_sqrt A hA,blockMatrix_sqrt B hB,blockMatrix_mul,blockMatrix_traceNorm]
  rfl

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetPowersStormerDiagonal -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α : Type} [Fintype α] [DecidableEq α]

def signReal (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma signReal_mul (x : ℝ) : signReal x*x=|x| := by
  by_cases h:0 ≤ x
  · simp [signReal,h,abs_of_nonneg h]
  · simp [signReal,h,abs_of_neg (lt_of_not_ge h)]

lemma signReal_sq (x : ℝ) : signReal x*signReal x=1 := by
  unfold signReal
  split_ifs <;> norm_num

lemma diagonal_sign_unitary (l : α→ℝ) :
    Matrix.diagonal (fun i=>(signReal (l i):ℂ))∈Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  simp only [Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [Pi.star_apply,Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,signReal_sq,Complex.ofReal_one]

/-- Powers–Størmer in a basis diagonalizing A−B. -/
theorem powers_stormer_diagonal (A B : Matrix α α ℂ) (hA:A.PosSemidef) (hB:B.PosSemidef)
    (l : α→ℝ) (hAB:A-B=Matrix.diagonal (fun i=>(l i:ℂ))) :
    (∑i,l i^2) ≤ WildeQIT.traceNorm (A*A-B*B) := by
  let D : Matrix α α ℂ := Matrix.diagonal (fun i=>(l i:ℂ))
  let S : Matrix α α ℂ := Matrix.diagonal (fun i=>(signReal (l i):ℂ))
  let E : Matrix α α ℂ := Matrix.diagonal (fun i=>((|l i|:ℝ):ℂ))
  let N : Matrix α α ℂ := A*A-B*B
  have hSD:S*D=E := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [← Complex.ofReal_mul,signReal_mul]
  have hDS:D*S=E := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Complex.ofReal_mul,mul_comm,signReal_mul]
  have hN:N=D*A+B*D := by
    change A*A-B*B= _
    have hD:A-B=D := hAB
    rw [← hD]
    noncomm_ring
  have htrace:(S*N).trace=(E*(A+B)).trace := by
    calc
      (S*N).trace=(S*D*A).trace+(S*B*D).trace := by
        rw [hN,Matrix.mul_add,Matrix.trace_add]
        simp only [Matrix.mul_assoc]
      _ = (E*A).trace+(E*B).trace := by rw [hSD,Matrix.trace_mul_cycle S B D,hDS]
      _ = _ := by rw [Matrix.mul_add,Matrix.trace_add]
  have ht:(E*(A+B)).trace.re=∑i,|l i| *((A i i).re+(B i i).re) := by
    simp [E,Matrix.trace,Matrix.diag,Matrix.diagonal_mul,Complex.mul_re]
  have hl:(∑i,l i^2) ≤ (S*N).trace.re := by
    rw [htrace,ht]
    apply Finset.sum_le_sum
    intro i hi
    have ha:0 ≤ (A i i).re := (Complex.nonneg_iff.mp (show 0 ≤ A i i from hA.diag_nonneg)).1
    have hb:0 ≤ (B i i).re := (Complex.nonneg_iff.mp (show 0 ≤ B i i from hB.diag_nonneg)).1
    have hd:=congrArg (fun M : Matrix α α ℂ=>(M i i).re) hAB
    simp only [Matrix.sub_apply,Complex.sub_re,Matrix.diagonal_apply_eq,Complex.ofReal_re] at hd
    by_cases hli:0 ≤ l i
    · rw [abs_of_nonneg hli]
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hli)]
      nlinarith
  have hdual:=traceNorm_dual N ⟨S,diagonal_sign_unitary l⟩
  have htn:(S*N).trace=(N*S).trace := Matrix.trace_mul_comm S N
  rw [htn] at hl
  exact hl.trans ((Complex.re_le_norm _).trans hdual)

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetPowersStormer -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma traceNorm_unitary_left (U : Matrix.unitaryGroup α ℂ) (A : Matrix α β ℂ) :
    WildeQIT.traceNorm ((U:Matrix α α ℂ)*A)=WildeQIT.traceNorm A := by
  have hh:(U:Matrix α α ℂ)ᴴ*(U:Matrix α α ℂ)=1 := Unitary.coe_star_mul_self U
  calc
    _ = WildeQIT.traceNorm (((U:Matrix α α ℂ)*A)ᴴ) := (traceNorm_conjTranspose _).symm
    _ = WildeQIT.traceNorm (Aᴴ*(U:Matrix α α ℂ)ᴴ) := by rw [Matrix.conjTranspose_mul]
    _ = WildeQIT.traceNorm Aᴴ := traceNorm_mul_coisometry _ _ (by simpa only [Matrix.conjTranspose_conjTranspose] using hh)
    _ = _ := traceNorm_conjTranspose A

lemma traceNorm_unitary_conjugate (U : Matrix.unitaryGroup α ℂ) (A : Matrix α α ℂ) :
    WildeQIT.traceNorm ((U:Matrix α α ℂ)ᴴ*A*(U:Matrix α α ℂ))=WildeQIT.traceNorm A := by
  rw [traceNorm_mul_coisometry _ _ (show (U:Matrix α α ℂ)*(U:Matrix α α ℂ)ᴴ=1 from Unitary.coe_mul_star_self U)]
  simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using traceNorm_unitary_left (star U) A

lemma trace_unitary_conjugate (U : Matrix.unitaryGroup α ℂ) (A : Matrix α α ℂ) :
    ((U:Matrix α α ℂ)ᴴ*A*(U:Matrix α α ℂ)).trace=A.trace := by
  rw [Matrix.trace_mul_cycle]
  have hh:(U:Matrix α α ℂ)*(U:Matrix α α ℂ)ᴴ=1 := Unitary.coe_mul_star_self U
  rw [hh,Matrix.one_mul]

lemma unitary_coisometry_cancel (U : Matrix.unitaryGroup α ℂ) (A : Matrix α α ℂ) :
    (U:Matrix α α ℂ)*((U:Matrix α α ℂ)ᴴ*A)=A := by
  rw [← Matrix.mul_assoc]
  have hh:(U:Matrix α α ℂ)*(U:Matrix α α ℂ)ᴴ=1 := Unitary.coe_mul_star_self U
  rw [hh,Matrix.one_mul]

lemma unitary_conjugate_mul (U : Matrix.unitaryGroup α ℂ) (A B : Matrix α α ℂ) :
    ((U:Matrix α α ℂ)ᴴ*A*(U:Matrix α α ℂ))*((U:Matrix α α ℂ)ᴴ*B*(U:Matrix α α ℂ))=
      (U:Matrix α α ℂ)ᴴ*(A*B)*(U:Matrix α α ℂ) := by
  simp only [Matrix.mul_assoc,unitary_coisometry_cancel]

/-- Finite-matrix Powers–Størmer inequality, in the exact public trace norm. -/
theorem powers_stormer (A B : Matrix α α ℂ) (hA:A.PosSemidef) (hB:B.PosSemidef) :
    ((A-B)*(A-B)).trace.re ≤ WildeQIT.traceNorm (A*A-B*B) := by
  let C := A-B
  have hC:C.IsHermitian := hA.isHermitian.sub hB.isHermitian
  let U := hC.eigenvectorUnitary
  let R : Matrix α α ℂ := (U:Matrix α α ℂ)ᴴ*A*(U:Matrix α α ℂ)
  let T : Matrix α α ℂ := (U:Matrix α α ℂ)ᴴ*B*(U:Matrix α α ℂ)
  let l := hC.eigenvalues
  have hR:R.PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hA.mul_mul_conjTranspose_same (U:Matrix α α ℂ)ᴴ
  have hT:T.PosSemidef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hB.mul_mul_conjTranspose_same (U:Matrix α α ℂ)ᴴ
  have hc:R-T=(U:Matrix α α ℂ)ᴴ*C*(U:Matrix α α ℂ) := by
    simp only [R,T,C,Matrix.mul_sub,Matrix.sub_mul]
  have hd:R-T=Matrix.diagonal (fun i=>(l i:ℂ)) := by
    rw [hc]
    simpa [U,l,Unitary.conjStarAlgAut_star_apply,Function.comp_def,Matrix.star_eq_conjTranspose]
      using hC.conjStarAlgAut_star_eigenvectorUnitary
  have hn:R*R-T*T=(U:Matrix α α ℂ)ᴴ*(A*A-B*B)*(U:Matrix α α ℂ) := by
    simp only [R,T,unitary_conjugate_mul,Matrix.mul_sub,Matrix.sub_mul]
  have htr:((A-B)*(A-B)).trace.re=(∑i,l i^2) := by
    have he:((R-T)*(R-T)).trace=((A-B)*(A-B)).trace := by
      rw [hc,unitary_conjugate_mul,trace_unitary_conjugate]
    rw [← he,hd,Matrix.diagonal_mul_diagonal,Matrix.trace_diagonal,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Complex.mul_re,pow_two]
  rw [htr]
  calc
    _ ≤ WildeQIT.traceNorm (R*R-T*T) := powers_stormer_diagonal R T hR hT l hd
    _ = _ := by rw [hn,traceNorm_unitary_conjugate]

/-- The lower Fuchs–van de Graaf bound needed in Theorem7, proved with
Powers–Størmer and not imported as an Open information-theory statement. -/
theorem rootFidelity_ge_one_sub_tdist (ρ σ : Matrix α α ℂ) (hρ:IsDensity ρ) (hσ:IsDensity σ) :
    1-tdist ρ σ ≤ rootFidelity ρ σ := by
  let A := CFC.sqrt ρ
  let B := CFC.sqrt σ
  have hA:A.PosSemidef := (CFC.sqrt_nonneg ρ).posSemidef
  have hB:B.PosSemidef := (CFC.sqrt_nonneg σ).posSemidef
  have hAA:A*A=ρ := CFC.sqrt_mul_sqrt_self _ hρ.1.nonneg
  have hBB:B*B=σ := CFC.sqrt_mul_sqrt_self _ hσ.1.nonneg
  have hh:=powers_stormer A B hA hB
  rw [hAA,hBB] at hh
  have hc:((A-B)*(A-B)).trace.re=2-2*(A*B).trace.re := by
    have he:(A-B)*(A-B)=A*A+B*B-A*B-B*A := by noncomm_ring
    rw [he,hAA,hBB,Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_add,
      hρ.2,hσ.2,Matrix.trace_mul_comm B A]
    simp [Complex.sub_re,Complex.add_re]
    ring
  rw [hc] at hh
  have hf:(A*B).trace.re ≤ rootFidelity ρ σ := by
    change (A*B).trace.re ≤ WildeQIT.traceNorm (A*B)
    rw [traceNorm_eq_left]
    exact CFCBasics.re_tr_le _
  unfold tdist
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetTraceDistance -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped MatrixOrder ComplexOrder
variable {α : Type} [Fintype α] [DecidableEq α]

lemma trace_mul_posSemidef_nonneg (A B : Matrix α α ℂ) (ha:A.PosSemidef) (hb:B.PosSemidef) :
    0 ≤ (A*B).trace.re := by
  let S := CFC.sqrt A
  have hs:Sᴴ=S := (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
  have ht:=hb.mul_mul_conjTranspose_same S
  have htr:0 ≤ (S*B*Sᴴ).trace.re := (Complex.nonneg_iff.mp ht.trace_nonneg).1
  rw [hs,Matrix.trace_mul_cycle] at htr
  change 0 ≤ ((CFC.sqrt A*CFC.sqrt A)*B).trace.re at htr
  rw [CFC.sqrt_mul_sqrt_self A ha.nonneg] at htr
  exact htr

lemma trace_mul_effect_le (P A : Matrix α α ℂ) (ha:A.PosSemidef)
    (hp:(1-P).PosSemidef) : (P*A).trace.re ≤ A.trace.re := by
  have ht:=trace_mul_posSemidef_nonneg (1-P) A hp ha
  simp only [sub_mul,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re] at ht
  linarith

/-- The sharp half-trace-norm variational bound for a traceless Hermitian
matrix, with an arbitrary matrix effect. -/
theorem trace_effect_le_half_traceNorm (H P : Matrix α α ℂ)
    (hH:H.IsHermitian) (htr:H.trace=0) (hp:P.PosSemidef) (hpc:(1-P).PosSemidef) :
    (P*H).trace.re ≤ WildeQIT.traceNorm H/2 := by
  have hpos:(H⁺).PosSemidef := (CFC.posPart_nonneg H).posSemidef
  have hneg:(H⁻).PosSemidef := (CFC.negPart_nonneg H).posSemidef
  have habs:CFC.abs H=H⁺+H⁻ := (CFC.posPart_add_negPart H hH.isSelfAdjoint).symm
  have hsplit:H=H⁺-H⁻ := (CFC.posPart_sub_negPart H hH.isSelfAdjoint).symm
  have heq:(H⁺).trace.re=(H⁻).trace.re := by
    have hh:=congrArg (fun M : Matrix α α ℂ=>M.trace.re) hsplit
    rw [htr,Matrix.trace_sub] at hh
    simp only [Complex.zero_re,Complex.sub_re] at hh
    linarith
  have hnorm:WildeQIT.traceNorm H=(H⁺).trace.re+(H⁻).trace.re := by
    change (CFC.abs H).trace.re= _
    rw [habs,Matrix.trace_add,Complex.add_re]
  have h1:=trace_mul_effect_le P H⁺ hpos hpc
  have h2:=trace_mul_posSemidef_nonneg P H⁻ hp hneg
  have h3:(P*H).trace.re=(P*H⁺).trace.re-(P*H⁻).trace.re := by
    conv_lhs => rw [hsplit]
    rw [mul_sub,Matrix.trace_sub,Complex.sub_re]
  linarith

/-- Outcome probabilities of an arbitrary effect differ by at most the
public trace distance of two equal-trace Hermitian matrices. -/
theorem trace_effect_sub_le_tdist (A B P : Matrix α α ℂ)
    (ha:A.IsHermitian) (hb:B.IsHermitian) (ht:A.trace=B.trace)
    (hp:P.PosSemidef) (hpc:(1-P).PosSemidef) :
    (P*(A-B)).trace.re ≤ tdist A B := by
  exact trace_effect_le_half_traceNorm (A-B) P (ha.sub hb) (by simp [ht]) hp hpc

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetFidelityClipping -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

lemma blockMatrix_sub (A B : ι→Matrix α α ℂ) :
    blockMatrix A-blockMatrix B=blockMatrix (fun i=>A i-B i) := by
  ext x y
  by_cases h:x.1=y.1 <;> simp [blockMatrix,h]

def labelEffect (p : ℝ) (Ω : ι→Matrix α α ℂ) : Matrix (ι×α) (ι×α) ℂ :=
  Matrix.diagonal (fun x=>if p<(Ω x.1).trace.re then 1 else 0)

lemma labelEffect_block (p : ℝ) (Ω : ι→Matrix α α ℂ) :
    labelEffect p Ω=blockMatrix (fun i=>if p<(Ω i).trace.re then 1 else 0) := by
  ext x y
  rcases x with ⟨i,a⟩
  rcases y with ⟨j,b⟩
  by_cases h:i=j
  · subst j
    by_cases hc:p<(Ω i).trace.re <;>
      simp [labelEffect,blockMatrix,Matrix.diagonal_apply,Matrix.one_apply,hc]
  · simp [labelEffect,blockMatrix,Matrix.diagonal_apply,Prod.ext_iff,h]

lemma labelEffect_posSemidef (p : ℝ) (Ω : ι→Matrix α α ℂ) : (labelEffect p Ω).PosSemidef := by
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro x
  split_ifs <;> norm_num

lemma labelEffect_compl_posSemidef (p : ℝ) (Ω : ι→Matrix α α ℂ) : (1-labelEffect p Ω).PosSemidef := by
  have he:(1-labelEffect p Ω)=Matrix.diagonal
      (fun x=>if p<(Ω x.1).trace.re then (0:ℂ) else 1) := by
    ext x y
    by_cases h:x=y <;> by_cases hc:p<(Ω x.1).trace.re <;> simp_all [labelEffect]
    all_goals try split_ifs
    all_goals aesop
  rw [he]
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro x
  split_ifs <;> norm_num

lemma clipping_mass_eq_trace (p : ℝ) (τ Ω : ι→Matrix α α ℂ)
    (hτ:∀i,(τ i).trace.re=p) :
    (labelEffect p Ω*(blockMatrix Ω-blockMatrix τ)).trace.re=
      ∑i,max ((Ω i).trace.re-p) 0 := by
  rw [labelEffect_block,blockMatrix_sub,blockMatrix_mul,blockMatrix_trace,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h:p<(Ω i).trace.re
  · rw [if_pos h,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re,hτ]
    exact (max_eq_left (by linarith : 0 ≤ (Ω i).trace.re-p)).symm
  · rw [if_neg h,Matrix.zero_mul,Matrix.trace_zero,Complex.zero_re]
    exact (max_eq_right (by linarith : (Ω i).trace.re-p ≤ 0)).symm

/-- Measuring only the excessive-mass classical labels charges clipping
mass directly to the original full quantum trace distance. -/
theorem clipping_mass_le_tdist (p : ℝ) (τ Ω : ι→Matrix α α ℂ)
    (hτ:∀i,(τ i).trace.re=p) (hτD:IsDensity (blockMatrix τ)) (hΩD:IsDensity (blockMatrix Ω)) :
    (∑i,max ((Ω i).trace.re-p) 0) ≤ tdist (blockMatrix Ω) (blockMatrix τ) := by
  have hh:=QuantumRankProof.trace_effect_sub_le_tdist (blockMatrix Ω) (blockMatrix τ) (labelEffect p Ω)
    hΩD.1.isHermitian hτD.1.isHermitian (hΩD.2.trans hτD.2.symm)
    (labelEffect_posSemidef p Ω) (labelEffect_compl_posSemidef p Ω)
  rwa [clipping_mass_eq_trace p τ Ω hτ] at hh

/-- Source Eq(7): clipping the ensemble to uniform label mass loses at most
an extra delta/2 in root fidelity. All density and block hypotheses here
are established directly for the actual ensemble in Theorem7. -/
theorem clipped_fidelity_bound (p : ℝ) (hp:0<p) (τ Ω : ι→Matrix α α ℂ)
    (hτ:∀i,(τ i).PosSemidef) (hΩ:∀i,(Ω i).PosSemidef) (htrace:∀i,(τ i).trace.re=p)
    (hτD:IsDensity (blockMatrix τ)) (hΩD:IsDensity (blockMatrix Ω)) :
    1-(3/2:ℝ)*tdist (blockMatrix Ω) (blockMatrix τ) ≤
      rootFidelity (blockMatrix τ)
        (blockMatrix (fun i=>clipCoefficient p (Ω i).trace.re • Ω i)) := by
  let c:=fun i=>clipCoefficient p (Ω i).trace.re
  have hc (i : ι) : 0 ≤ c i := clipCoefficient_nonneg p _ hp (CFCBasics.psd_re (hΩ i))
  have hclip (i : ι) : (c i • Ω i).PosSemidef := (hΩ i).smul (hc i)
  have heach (i : ι) : rootFidelity (τ i) (Ω i)-rootFidelity (τ i) (c i • Ω i) ≤
      max ((Ω i).trace.re-p) 0/2 := by
    rw [rootFidelity_smul_right _ _ (hΩ i) _ (hc i)]
    apply clipping_loss p (Ω i).trace.re _ hp (CFCBasics.psd_re (hΩ i))
    have hh:=rootFidelity_trace_bound _ _ (hτ i) (hΩ i)
    rwa [htrace] at hh
  have hsum:=Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset ι))=>heach i)
  rw [Finset.sum_sub_distrib,← Finset.sum_div] at hsum
  have hm:=clipping_mass_le_tdist p τ Ω htrace hτD hΩD
  have hf:=rootFidelity_ge_one_sub_tdist (blockMatrix Ω) (blockMatrix τ) hΩD hτD
  rw [rootFidelity_symm (blockMatrix Ω) (blockMatrix τ)] at hf
  rw [rootFidelity_blockMatrix τ Ω hτ hΩ] at hf
  change _ ≤ rootFidelity (blockMatrix τ) (blockMatrix (fun i=>c i • Ω i))
  rw [rootFidelity_blockMatrix τ _ hτ hclip]
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetGentleFilter -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α : Type} [Fintype α] [DecidableEq α]

lemma effect_eigenvalues_le_one (E : Matrix α α ℂ) (hE:E.PosSemidef) (hc:(1-E).PosSemidef) (i : α) :
    hE.isHermitian.eigenvalues i ≤ 1 := by
  let U:=hE.isHermitian.eigenvectorUnitary
  have he:(U:Matrix α α ℂ)ᴴ*E*(U:Matrix α α ℂ)=
      Matrix.diagonal (fun i=>(hE.isHermitian.eigenvalues i:ℂ)) := by
    simpa [U,Unitary.conjStarAlgAut_star_apply,Function.comp_def,Matrix.star_eq_conjTranspose]
      using hE.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hh:=hc.mul_mul_conjTranspose_same (U:Matrix α α ℂ)ᴴ
  rw [Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,he] at hh
  have hu:(U:Matrix α α ℂ)ᴴ*(U:Matrix α α ℂ)=1 := Unitary.coe_star_mul_self U
  rw [hu] at hh
  have hd:0 ≤ (1-Matrix.diagonal (fun i=>(hE.isHermitian.eigenvalues i:ℂ))) i i := hh.diag_nonneg
  have hr:0 ≤ ((1-Matrix.diagonal (fun i=>(hE.isHermitian.eigenvalues i:ℂ))) i i).re :=
    (Complex.nonneg_iff.mp hd).1
  simp only [Matrix.sub_apply,Matrix.one_apply_eq,Matrix.diagonal_apply_eq,Complex.sub_re,Complex.one_re,
    Complex.ofReal_re] at hr
  linarith

lemma effect_sqrt_sub_posSemidef (E : Matrix α α ℂ) (hE:E.PosSemidef) (hc:(1-E).PosSemidef) :
    (CFC.sqrt E-E).PosSemidef := by
  have he:CFC.sqrt E-E=cfc (fun x:ℝ=>Real.sqrt x-x) E := by
    rw [sqrt_eq_cfc E hE,cfc_sub _ _ _ (CFCBasics.fin _ _) (CFCBasics.fin _ _),
      cfc_id' ℝ E hE.isHermitian.isSelfAdjoint]
  rw [he]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply cfc_nonneg
  intro x hx
  rw [hE.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i,rfl⟩:=hx
  have h0:=hE.eigenvalues_nonneg i
  have h1:=effect_eigenvalues_le_one E hE hc i
  have hs:=Real.mul_self_sqrt h0
  have hn:=Real.sqrt_nonneg (hE.isHermitian.eigenvalues i)
  nlinarith [mul_nonneg h0 (show 0 ≤ 1-hE.isHermitian.eigenvalues i by linarith)]

/-- The soft-filter inequality (I−sqrt E)^2 ≤ I−E for a genuine matrix effect. -/
lemma effect_filter_difference (E : Matrix α α ℂ) (hE:E.PosSemidef) (hc:(1-E).PosSemidef) :
    ((1-E)-(1-CFC.sqrt E)*(1-CFC.sqrt E)).PosSemidef := by
  have he:(1-E)-(1-CFC.sqrt E)*(1-CFC.sqrt E)=(2:ℝ) • (CFC.sqrt E-E) := by
    have hs:=CFC.sqrt_mul_sqrt_self E hE.nonneg
    rw [two_smul]
    noncomm_ring [hs]
  rw [he]
  exact (effect_sqrt_sub_posSemidef E hE hc).smul (by norm_num : (0:ℝ) ≤ 2)

/-- The unnormalized gentle-filter estimate, in Hilbert–Schmidt norm. -/
theorem gentle_filter (E ρ : Matrix α α ℂ) (hE:E.PosSemidef) (hc:(1-E).PosSemidef) (hρ:ρ.PosSemidef) :
    hsNorm ((1-CFC.sqrt E)*CFC.sqrt ρ) ≤ Real.sqrt ((1-E)*ρ).trace.re := by
  let R:=CFC.sqrt ρ
  let F:=1-CFC.sqrt E
  have hR:Rᴴ=R := (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq
  have hF:Fᴴ=F := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one]
    exact congrArg (fun X:Matrix α α ℂ=>1-X) (CFC.sqrt_nonneg E).isSelfAdjoint.star_eq
  have hh:((1-E)-F*F).PosSemidef := effect_filter_difference E hE hc
  have ht:=CFCBasics.psd_re (hh.mul_mul_conjTranspose_same R)
  rw [hR,Matrix.mul_sub,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re] at ht
  have hRR:R*R=ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hleft:(R*(1-E)*R).trace=((1-E)*ρ).trace := by
    rw [Matrix.trace_mul_cycle,hRR,Matrix.trace_mul_comm]
  have hright:(R*(F*F)*R).trace=((F*R)ᴴ*(F*R)).trace := by
    simp only [Matrix.conjTranspose_mul,hR,hF,Matrix.mul_assoc]
  rw [hleft,hright] at ht
  apply Real.sqrt_le_sqrt
  change ((F*R)ᴴ*(F*R)).trace.re ≤ ((1-E)*ρ).trace.re
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetHilbertSchmidtOperations -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

lemma hsNorm_add_le (A B : Matrix α β ℂ) : hsNorm (A+B) ≤ hsNorm A+hsNorm B := by
  rw [hsNorm_eq_norm,hsNorm_eq_norm,hsNorm_eq_norm]
  have he:entryVector (A+B)=entryVector A+entryVector B := rfl
  rw [he]
  exact norm_add_le _ _

lemma hsNorm_isometry_left (V : Matrix α β ℂ) (hV:Vᴴ*V=1) (A : Matrix β γ ℂ) :
    hsNorm (V*A)=hsNorm A := by
  have hg:(V*A)ᴴ*(V*A)=Aᴴ*A := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V A,hV,Matrix.one_mul]
  rw [hsNorm,hg]
  rfl

lemma hsNorm_contraction_left (K : Matrix α β ℂ) (hK:(1-Kᴴ*K).PosSemidef) (A : Matrix β γ ℂ) :
    hsNorm (K*A) ≤ hsNorm A := by
  have ht:=CFCBasics.psd_re (hK.mul_mul_conjTranspose_same Aᴴ)
  rw [Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,
    Matrix.trace_sub,Complex.sub_re] at ht
  have hg:(K*A)ᴴ*(K*A)=Aᴴ*(Kᴴ*K)*A := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  unfold hsNorm
  apply Real.sqrt_le_sqrt
  rw [hg]
  linarith

/-- Gentle filtering for any explicit purification factor, with no
normalization or rank assumption on its column space. -/
theorem gentle_filter_factor (E : Matrix α α ℂ) (hE:E.PosSemidef) (hc:(1-E).PosSemidef)
    (A : Matrix α β ℂ) :
    hsNorm ((1-CFC.sqrt E)*A) ≤ Real.sqrt ((1-E)*(A*Aᴴ)).trace.re := by
  let F:Matrix α α ℂ:=1-CFC.sqrt E
  have hF:Fᴴ=F := by
    rw [Matrix.conjTranspose_sub,Matrix.conjTranspose_one]
    exact congrArg (fun X:Matrix α α ℂ=>1-X) (CFC.sqrt_nonneg E).isSelfAdjoint.star_eq
  have hh:((1-E)-F*F).PosSemidef := effect_filter_difference E hE hc
  have ht:=CFCBasics.psd_re (hh.mul_mul_conjTranspose_same Aᴴ)
  rw [Matrix.conjTranspose_conjTranspose,Matrix.mul_sub,Matrix.sub_mul,Matrix.trace_sub,Complex.sub_re] at ht
  have he:(Aᴴ*(1-E)*A).trace=((1-E)*(A*Aᴴ)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have hg:(F*A)ᴴ*(F*A)=Aᴴ*(F*F)*A := by simp only [Matrix.conjTranspose_mul,hF,Matrix.mul_assoc]
  unfold hsNorm
  apply Real.sqrt_le_sqrt
  change ((F*A)ᴴ*(F*A)).trace.re ≤ _
  rw [hg]
  rw [he] at ht
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetFidelityFactorLipschitz -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A single explicit purification factor suffices, even when its column
space has a different dimension from the normalized comparison state. -/
theorem rootFidelity_right_factor (ρ : Matrix α α ℂ) (A : Matrix α β ℂ) :
    rootFidelity ρ (A*Aᴴ)=WildeQIT.traceNorm (CFC.sqrt ρ*A) := by
  let S:=CFC.sqrt ρ
  let T:=CFC.sqrt (A*Aᴴ)
  have hS:Sᴴ=S := (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq
  have hT:Tᴴ=T := (CFC.sqrt_nonneg (A*Aᴴ)).isSelfAdjoint.star_eq
  have hTT:T*T=A*Aᴴ := CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_self_mul_conjTranspose A).nonneg
  change WildeQIT.traceNorm (S*T)=_
  calc
    _ = WildeQIT.traceNorm (Aᴴ*S) := traceNorm_swap_grams _ _ (by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,hS,hT]
      simp only [Matrix.mul_assoc,← Matrix.mul_assoc T T,hTT])
    _ = WildeQIT.traceNorm (S*A) := by
      rw [← traceNorm_conjTranspose (Aᴴ*S)]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,hS]

/-- Fidelity is Lipschitz in an arbitrary purification factor, with
constant one for a density comparison state. -/
theorem rootFidelity_right_factor_lipschitz (ρ : Matrix α α ℂ) (hρ:IsDensity ρ)
    (A B : Matrix α β ℂ) :
    rootFidelity ρ (A*Aᴴ)-hsNorm (A-B) ≤ rootFidelity ρ (B*Bᴴ) := by
  rw [rootFidelity_right_factor,rootFidelity_right_factor]
  have hn:hsNorm (CFC.sqrt ρ)=1 := by rw [hsNorm_sqrt ρ hρ.1,hρ.2];norm_num
  have hd:=traceNorm_mul_le_hs (CFC.sqrt ρ) (A-B)
  rw [hn,one_mul] at hd
  have he:CFC.sqrt ρ*A=CFC.sqrt ρ*B+CFC.sqrt ρ*(A-B) := by rw [Matrix.mul_sub];abel
  have ht:=traceNorm_add_le (CFC.sqrt ρ*B) (CFC.sqrt ρ*(A-B))
  rw [← he] at ht
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetTwoFilterDisturbance -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-- The second filter is compared to the unfiltered input. This avoids any
assumption that the first filtering preserves the second decoder's success. -/
theorem two_filter_disturbance (V : Matrix β α ℂ) (hV:Vᴴ*V=1)
    (E : Matrix α α ℂ) (F : Matrix β β ℂ)
    (hE:E.PosSemidef) (hcE:(1-E).PosSemidef) (hF:F.PosSemidef) (hcF:(1-F).PosSemidef)
    (A : Matrix α γ ℂ) :
    hsNorm (V*A-CFC.sqrt F*V*CFC.sqrt E*A) ≤
      Real.sqrt ((1-E)*(A*Aᴴ)).trace.re +
      Real.sqrt ((1-F)*(V*A*(V*A)ᴴ)).trace.re := by
  let K:=CFC.sqrt F
  have hK:(1-Kᴴ*K).PosSemidef := by
    have hk:Kᴴ=K := (CFC.sqrt_nonneg F).isSelfAdjoint.star_eq
    rw [hk,CFC.sqrt_mul_sqrt_self F hF.nonneg]
    exact hcF
  have hde:=gentle_filter_factor E hE hcE A
  have hdf:=gentle_filter_factor F hF hcF (V*A)
  have he:V*A-K*V*CFC.sqrt E*A=(1-K)*(V*A)+K*(V*((1-CFC.sqrt E)*A)) := by
    dsimp [K]
    simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    abel
  rw [he]
  have ht:=hsNorm_add_le ((1-K)*(V*A)) (K*(V*((1-CFC.sqrt E)*A)))
  have hc:=hsNorm_contraction_left K hK (V*((1-CFC.sqrt E)*A))
  rw [hsNorm_isometry_left V hV] at hc
  exact ht.trans (by dsimp [K] at *;linarith)

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetQuantumRankBasics -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SpaceReset.Hardness.QuantumRankProof
open Matrix Classical
open scoped ComplexOrder MatrixOrder

variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

lemma matrix_rank_add_le (A B : Matrix α β ℂ) : (A+B).rank ≤ A.rank+B.rank := by
  rw [Matrix.rank,Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

lemma matrix_rank_sum_le {ι : Type} (S : Finset ι) (A : ι→Matrix α β ℂ) :
    (∑ i∈S,A i).rank ≤ ∑ i∈S,(A i).rank := by
  induction S using Finset.cons_induction with
  | empty => simp
  | @cons i S hi ih =>
    rw [Finset.sum_cons hi,Finset.sum_cons hi]
    exact (matrix_rank_add_le _ _).trans (Nat.add_le_add_left ih _)

lemma ptraceRight_eq_sum (ρ : Matrix (α×β) (α×β) ℂ) :
    ptraceRight ρ=∑ b:β,ρ.submatrix (fun a=>(a,b)) (fun a=>(a,b)) := by
  ext a a'
  simp [ptraceRight,Matrix.sum_apply]

lemma ptraceLeft_eq_sum (ρ : Matrix (α×β) (α×β) ℂ) :
    ptraceLeft ρ=∑ a:α,ρ.submatrix (fun b=>(a,b)) (fun b=>(a,b)) := by
  ext b b'
  simp [ptraceLeft,Matrix.sum_apply]

/-- Tracing out a d-dimensional factor multiplies rank by at most d. -/
theorem rank_ptraceRight_le (ρ : Matrix (α×β) (α×β) ℂ) :
    (ptraceRight ρ).rank ≤ Fintype.card β*ρ.rank := by
  rw [ptraceRight_eq_sum]
  exact (matrix_rank_sum_le _ _).trans ((Finset.sum_le_sum (fun b hb=>Matrix.rank_submatrix_le _ _ _)).trans_eq
    (by simp [Nat.mul_comm]))

theorem rank_ptraceLeft_le (ρ : Matrix (α×β) (α×β) ℂ) :
    (ptraceLeft ρ).rank ≤ Fintype.card α*ρ.rank := by
  rw [ptraceLeft_eq_sum]
  exact (matrix_rank_sum_le _ _).trans ((Finset.sum_le_sum (fun b hb=>Matrix.rank_submatrix_le _ _ _)).trans_eq
    (by simp [Nat.mul_comm]))

lemma ptraceRight_posSemidef (ρ : Matrix (α×β) (α×β) ℂ) (hρ:ρ.PosSemidef) :
    (ptraceRight ρ).PosSemidef := by
  rw [ptraceRight_eq_sum]
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun b hb=>(hρ.submatrix _).nonneg)

lemma ptraceLeft_posSemidef (ρ : Matrix (α×β) (α×β) ℂ) (hρ:ρ.PosSemidef) :
    (ptraceLeft ρ).PosSemidef := by
  rw [ptraceLeft_eq_sum]
  apply Matrix.nonneg_iff_posSemidef.mp
  exact Finset.sum_nonneg (fun a ha=>(hρ.submatrix _).nonneg)

lemma trace_ptraceRight (ρ : Matrix (α×β) (α×β) ℂ) : (ptraceRight ρ).trace=ρ.trace := by
  change (∑ a,∑ b,ρ (a,b) (a,b))=(∑ x:α×β,ρ x x)
  rw [Fintype.sum_prod_type]

lemma trace_ptraceLeft (ρ : Matrix (α×β) (α×β) ℂ) : (ptraceLeft ρ).trace=ρ.trace := by
  change (∑ b,∑ a,ρ (a,b) (a,b))=(∑ x:α×β,ρ x x)
  rw [Fintype.sum_prod_type,Finset.sum_comm]

lemma rank_kraus_le {ι : Type} [Fintype ι] (K : ι→Matrix β α ℂ) (ρ : Matrix α α ℂ) :
    (∑ i,K i*ρ*(K i)ᴴ).rank ≤ Fintype.card ι*ρ.rank := by
  exact (matrix_rank_sum_le _ _).trans ((Finset.sum_le_sum (fun i hi=>
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))).trans_eq (by simp [Nat.mul_comm]))

lemma DiscardDevice_slot_rank {n q g : ℕ} (D : DiscardDevice n q g) (j : Fin n)
    (ρ : Matrix (Bool×D.M) (Bool×D.M) ℂ) :
    (D.slot j ρ).rank ≤ Fintype.card (D.E j)*ρ.rank := by
  exact (rank_ptraceRight_le _).trans (Nat.mul_le_mul_left _
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)))

end SpaceReset.Hardness.QuantumRankProof

/- Module SpaceResetPurificationCoefficients -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {Y E R : Type} [Fintype Y] [DecidableEq Y] [Fintype E] [DecidableEq E]
  [Fintype R] [DecidableEq R]

/-- The same purification, with the emitted and environmental coordinates
viewed as matrix row and column indices. -/
def coefficient (A : Matrix (Y×E) R ℂ) : Matrix Y (E×R) ℂ := fun y er=>A (y,er.1) er.2

lemma coefficient_add (A B : Matrix (Y×E) R ℂ) : coefficient (A+B)=coefficient A+coefficient B := rfl
lemma coefficient_sub (A B : Matrix (Y×E) R ℂ) : coefficient (A-B)=coefficient A-coefficient B := rfl
lemma coefficient_smul (r : ℝ) (A : Matrix (Y×E) R ℂ) : coefficient (r • A)=r • coefficient A := rfl

lemma coefficient_gram (A : Matrix (Y×E) R ℂ) :
    coefficient A*(coefficient A)ᴴ=ptraceRight (A*Aᴴ) := by
  ext y z
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,coefficient,ptraceRight,Fintype.sum_prod_type]

lemma hsNorm_coefficient (A : Matrix (Y×E) R ℂ) : hsNorm (coefficient A)=hsNorm A := by
  unfold hsNorm
  congr 2
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,coefficient,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]

lemma hsNorm_coefficient_sub (A B : Matrix (Y×E) R ℂ) :
    hsNorm (coefficient A-coefficient B)=hsNorm (A-B) := by rw [← coefficient_sub,hsNorm_coefficient]

/-- Coefficient nuclear norm is the exact trace of the square root of the
output marginal; the environment is retained only mathematically. -/
lemma coefficient_traceNorm (A : Matrix (Y×E) R ℂ) :
    WildeQIT.traceNorm (coefficient A)=(CFC.sqrt (ptraceRight (A*Aᴴ))).trace.re := by
  rw [traceNorm_eq_left,coefficient_gram,
    ← sqrt_eq_cfc _ (QuantumRankProof.ptraceRight_posSemidef _ (Matrix.posSemidef_self_mul_conjTranspose A))]

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetFidelitySubnormalized -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The comparison state may be subnormalized; its trace supplies the
precise scaling factor in the purification disturbance estimate. -/
theorem rootFidelity_right_factor_lipschitz_subnormalized (ρ : Matrix α α ℂ)
    (hρ:ρ.PosSemidef) (A B : Matrix α β ℂ) :
    rootFidelity ρ (A*Aᴴ)-Real.sqrt ρ.trace.re*hsNorm (A-B) ≤ rootFidelity ρ (B*Bᴴ) := by
  rw [rootFidelity_right_factor,rootFidelity_right_factor]
  have hd:=traceNorm_mul_le_hs (CFC.sqrt ρ) (A-B)
  rw [hsNorm_sqrt ρ hρ] at hd
  have he:CFC.sqrt ρ*A=CFC.sqrt ρ*B+CFC.sqrt ρ*(A-B) := by rw [Matrix.mul_sub];abel
  have ht:=traceNorm_add_le (CFC.sqrt ρ*B) (CFC.sqrt ρ*(A-B))
  rw [← he] at ht
  linarith

/-- A target bounded by r squared times the identity has fidelity at most
r times the trace of the square root of the compared state. -/
theorem rootFidelity_spectral_upper (ρ σ : Matrix α α ℂ) (hρ:ρ.PosSemidef) (hσ:σ.PosSemidef)
    (r : ℝ) (hr:0 ≤ r) (hb:((r^2:ℝ) • (1:Matrix α α ℂ)-ρ).PosSemidef) :
    rootFidelity ρ σ ≤ r*(CFC.sqrt σ).trace.re := by
  have he:(CFC.sqrt ρ)ᴴ*CFC.sqrt ρ=ρ := by
    have hs:(CFC.sqrt ρ)ᴴ=CFC.sqrt ρ := (CFC.sqrt_nonneg ρ).isSelfAdjoint.star_eq
    rw [hs,CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
  unfold rootFidelity
  have hh:=traceNorm_mul_left_le (CFC.sqrt ρ) (CFC.sqrt σ) r hr (by rwa [he])
  rwa [traceNorm_of_posSemidef _ (CFC.sqrt_nonneg σ).posSemidef] at hh

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetTwoFilterFidelity -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker
variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype E] [DecidableEq E]

lemma sqrt_gram (ξ : Matrix X X ℂ) (hξ:ξ.PosSemidef) :
    CFC.sqrt ξ*(CFC.sqrt ξ)ᴴ=ξ := by
  have hs:(CFC.sqrt ξ)ᴴ=CFC.sqrt ξ := (CFC.sqrt_nonneg ξ).isSelfAdjoint.star_eq
  rw [hs,CFC.sqrt_mul_sqrt_self ξ hξ.nonneg]

lemma isometry_sqrt_gram (V : Matrix Y X ℂ) (ξ : Matrix X X ℂ) (hξ:ξ.PosSemidef) :
    V*CFC.sqrt ξ*(V*CFC.sqrt ξ)ᴴ=V*ξ*Vᴴ := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc (CFC.sqrt ξ) (CFC.sqrt ξ)ᴴ,sqrt_gram ξ hξ]

/-- Blockwise form of source Eq(8), before summing the label-wise
Cauchy--Schwarz bounds. Both decoder errors refer to the original input. -/
theorem two_filter_fidelity_block (τ : Matrix Y Y ℂ) (hτ:τ.PosSemidef)
    (ξ : Matrix X X ℂ) (hξ:ξ.PosSemidef)
    (V : Matrix (Y×E) X ℂ) (hV:Vᴴ*V=1)
    (D : Matrix X X ℂ) (hD:D.PosSemidef) (hcD:(1-D).PosSemidef)
    (F : Matrix (Y×E) (Y×E) ℂ) (hF:F.PosSemidef) (hcF:(1-F).PosSemidef) :
    let B:=CFC.sqrt F*V*CFC.sqrt D*CFC.sqrt ξ
    rootFidelity τ (ptraceRight (V*ξ*Vᴴ))-
      Real.sqrt τ.trace.re*(Real.sqrt ((1-D)*ξ).trace.re+
        Real.sqrt ((1-F)*(V*ξ*Vᴴ)).trace.re) ≤
      rootFidelity τ (ptraceRight (B*Bᴴ)) := by
  dsimp only
  let A:=V*CFC.sqrt ξ
  let B:=CFC.sqrt F*V*CFC.sqrt D*CFC.sqrt ξ
  have hd:=two_filter_disturbance V hV D F hD hcD hF hcF (CFC.sqrt ξ)
  rw [sqrt_gram ξ hξ,isometry_sqrt_gram V ξ hξ] at hd
  have hf:=rootFidelity_right_factor_lipschitz_subnormalized τ hτ (coefficient A) (coefficient B)
  rw [coefficient_gram,coefficient_gram,hsNorm_coefficient_sub] at hf
  have ha:A*Aᴴ=V*ξ*Vᴴ := isometry_sqrt_gram V ξ hξ
  rw [ha] at hf
  have hm:=mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg τ.trace.re)
  change rootFidelity τ (ptraceRight (V*ξ*Vᴴ))-_ ≤ rootFidelity τ (ptraceRight (B*Bᴴ))
  change hsNorm (A-B) ≤ _ at hd
  change Real.sqrt τ.trace.re*hsNorm (A-B) ≤ _ at hm
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetEnsembleBasics -/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker
variable {ι α β : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
  [Fintype β] [DecidableEq β]

lemma povm_compl_posSemidef (E : ι→Matrix α α ℂ) (hE:IsPOVM E) (i : ι) :
    (1-E i).PosSemidef := by
  have hh:=Finset.sum_erase_add (Finset.univ:Finset ι) E (Finset.mem_univ i)
  rw [hE.2] at hh
  have he:1-E i=∑j∈Finset.univ.erase i,E j := by rw [← hh];abel
  rw [he]
  exact (Finset.sum_nonneg (fun j hj=>(hE.1 j).nonneg)).posSemidef

lemma output_effect_compl (F : Matrix β β ℂ) (hF:(1-F).PosSemidef) :
    (1-(1:Matrix α α ℂ) ⊗ₖ F).PosSemidef := by
  have he:(1:Matrix (α×β) (α×β) ℂ)-(1:Matrix α α ℂ) ⊗ₖ F=
      (1:Matrix α α ℂ) ⊗ₖ (1-F) := by
    rw [← Matrix.one_kronecker_one (m:=α) (n:=β) (α:=ℂ)]
    ext ⟨a,b⟩ ⟨c,d⟩
    simp only [Matrix.kronecker_apply,Matrix.sub_apply,mul_sub]
  rw [he]
  exact Matrix.PosSemidef.one.kronecker hF

lemma output_effect_sqrt (F : Matrix β β ℂ) (hF:F.PosSemidef) :
    CFC.sqrt ((1:Matrix α α ℂ) ⊗ₖ F)=(1:Matrix α α ℂ) ⊗ₖ CFC.sqrt F := by
  let K:Matrix (α×β) (α×β) ℂ:=(1:Matrix α α ℂ) ⊗ₖ CFC.sqrt F
  have h1:(1:Matrix α α ℂ).PosSemidef := Matrix.PosSemidef.one
  have hK:K.PosSemidef := h1.kronecker (CFC.sqrt_nonneg F).posSemidef
  have hKK:K*K=(1:Matrix α α ℂ) ⊗ₖ F := by
    dsimp only [K]
    rw [← Matrix.mul_kronecker_mul,Matrix.one_mul,CFC.sqrt_mul_sqrt_self F hF.nonneg]
  exact CFC.sqrt_unique hKK hK.nonneg

lemma trace_isometry (V : Matrix β α ℂ) (hV:Vᴴ*V=1) (ξ : Matrix α α ℂ) :
    (V*ξ*Vᴴ).trace=ξ.trace := by rw [Matrix.trace_mul_cycle,hV,Matrix.one_mul]

lemma ptraceRight_smul {γ : Type} [Fintype γ] (r : ℝ) (ρ : Matrix (α×γ) (α×γ) ℂ) :
    ptraceRight (r • ρ)=r • ptraceRight ρ := by
  ext a b
  simp [ptraceRight,Finset.smul_sum]

lemma blockMatrix_density (ξ : ι→Matrix α α ℂ) (hξ:∀i,(ξ i).PosSemidef)
    (h1:∑i,(ξ i).trace=1) : IsDensity (blockMatrix ξ) :=
  ⟨blockMatrix_posSemidef ξ hξ,by rwa [blockMatrix_trace]⟩

lemma blockMatrix_isometry_marginal_density {Y E : Type} [Fintype Y] [DecidableEq Y]
    [Fintype E] [DecidableEq E]
    (ξ : ι→Matrix α α ℂ) (hξ:∀i,(ξ i).PosSemidef) (h1:∑i,(ξ i).trace=1)
    (V : Matrix (Y×E) α ℂ) (hV:Vᴴ*V=1) :
    IsDensity (blockMatrix (fun i=>ptraceRight (V*ξ i*Vᴴ))) := by
  apply blockMatrix_density
  · intro i
    exact QuantumRankProof.ptraceRight_posSemidef _ ((hξ i).mul_mul_conjTranspose_same V)
  · simpa only [QuantumRankProof.trace_ptraceRight,trace_isometry V hV] using h1

lemma trace_psd_real (ξ : Matrix α α ℂ) (hξ:ξ.PosSemidef) :
    ξ.trace=(ξ.trace.re:ℂ) := by
  have hs:star ξ.trace=ξ.trace := by rw [← Matrix.trace_conjTranspose,hξ.isHermitian.eq]
  have hi:=congrArg Complex.im hs
  simp only [Complex.star_def,Complex.conj_im] at hi
  refine Complex.ext ?_ ?_
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

lemma failure_trace_nonneg (E ξ : Matrix α α ℂ) (hE:(1-E).PosSemidef) (hξ:ξ.PosSemidef) :
    0 ≤ ((1-E)*ξ).trace.re := QuantumRankProof.trace_mul_posSemidef_nonneg _ _ hE hξ

lemma clipping_failure_le (p : ℝ) (hp:0<p) (ξ E : Matrix α α ℂ) (hξ:ξ.PosSemidef)
    (hE:(1-E).PosSemidef) :
    ((1-E)*(clipCoefficient p ξ.trace.re • ξ)).trace.re ≤ ((1-E)*ξ).trace.re := by
  rw [Matrix.mul_smul,Matrix.trace_smul,Complex.real_smul]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_le_of_le_one_left (failure_trace_nonneg E ξ hE hξ)
    (clipCoefficient_le_one p _ hp (CFCBasics.psd_re hξ))

lemma failure_sum_eq (ξ E : ι→Matrix α α ℂ) (hξ1:∑i,(ξ i).trace=1) :
    (∑i,((1-E i)*ξ i).trace.re)=1-(∑i,(E i*ξ i).trace).re := by
  simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.trace_sub,Complex.sub_re,Finset.sum_sub_distrib]
  rw [← Complex.re_sum,hξ1,Complex.one_re,Complex.re_sum]

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetFilteredEnsemble -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker
variable {ι X Y E : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype E] [DecidableEq E]

/-- Source Eq(8): summing the blockwise purification estimate gives the two
square-root errors. The comparison ensemble is normalized as a whole. -/
theorem filtered_ensemble_fidelity (τ : ι→Matrix Y Y ℂ) (hτ:∀i,(τ i).PosSemidef)
    (hτ1:∑i,(τ i).trace.re=1) (ξ : ι→Matrix X X ℂ) (hξ:∀i,(ξ i).PosSemidef)
    (V : Matrix (Y×E) X ℂ) (hV:Vᴴ*V=1)
    (D : ι→Matrix X X ℂ) (hD:∀i,(D i).PosSemidef) (hcD:∀i,(1-D i).PosSemidef)
    (F : ι→Matrix (Y×E) (Y×E) ℂ) (hF:∀i,(F i).PosSemidef)
    (hcF:∀i,(1-F i).PosSemidef) (e₀ e₁ : ℝ)
    (he₀:(∑i,((1-D i)*ξ i).trace.re) ≤ e₀)
    (he₁:(∑i,((1-F i)*(V*ξ i*Vᴴ)).trace.re) ≤ e₁) :
    let B:=fun i=>CFC.sqrt (F i)*V*CFC.sqrt (D i)*CFC.sqrt (ξ i)
    rootFidelity (blockMatrix τ) (blockMatrix (fun i=>ptraceRight (V*ξ i*Vᴴ)))-
      Real.sqrt e₀-Real.sqrt e₁ ≤
      rootFidelity (blockMatrix τ) (blockMatrix (fun i=>ptraceRight (B i*(B i)ᴴ))) := by
  dsimp only
  let a:=fun i=>((1-D i)*ξ i).trace.re
  let b:=fun i=>((1-F i)*(V*ξ i*Vᴴ)).trace.re
  have ha:∀i,0 ≤ a i := fun i=>failure_trace_nonneg (D i) (ξ i) (hcD i) (hξ i)
  have hb:∀i,0 ≤ b i := fun i=>failure_trace_nonneg (F i) _ (hcF i)
    ((hξ i).mul_mul_conjTranspose_same V)
  have ht:∀i,0 ≤ (τ i).trace.re := fun i=>CFCBasics.psd_re (hτ i)
  have hsum:=Finset.sum_le_sum (fun i (_:i∈(Finset.univ:Finset ι))=>
    two_filter_fidelity_block (τ i) (hτ i) (ξ i) (hξ i) V hV
      (D i) (hD i) (hcD i) (F i) (hF i) (hcF i))
  have hca:=Real.sum_sqrt_mul_sqrt_le (Finset.univ:Finset ι) ht ha
  have hcb:=Real.sum_sqrt_mul_sqrt_le (Finset.univ:Finset ι) ht hb
  simp only [Finset.sum_sub_distrib,mul_add,Finset.sum_add_distrib] at hsum
  simp only [hτ1,Real.sqrt_one,one_mul] at hca hcb
  have hca':(∑i,Real.sqrt (τ i).trace.re*Real.sqrt (a i)) ≤ Real.sqrt e₀ :=
    hca.trans (Real.sqrt_le_sqrt he₀)
  have hcb':(∑i,Real.sqrt (τ i).trace.re*Real.sqrt (b i)) ≤ Real.sqrt e₁ :=
    hcb.trans (Real.sqrt_le_sqrt he₁)
  have hΩ:∀i,(ptraceRight (V*ξ i*Vᴴ)).PosSemidef := fun i=>
    QuantumRankProof.ptraceRight_posSemidef _ ((hξ i).mul_mul_conjTranspose_same V)
  have hζ:∀i,(ptraceRight ((CFC.sqrt (F i)*V*CFC.sqrt (D i)*CFC.sqrt (ξ i))*
      (CFC.sqrt (F i)*V*CFC.sqrt (D i)*CFC.sqrt (ξ i))ᴴ)).PosSemidef := fun i=>
    QuantumRankProof.ptraceRight_posSemidef _ (Matrix.posSemidef_self_mul_conjTranspose _)
  rw [rootFidelity_blockMatrix τ _ hτ hΩ,rootFidelity_blockMatrix τ _ hτ hζ]
  change (∑i,rootFidelity (τ i) (ptraceRight (V*ξ i*Vᴴ)))-Real.sqrt e₀-Real.sqrt e₁ ≤ _
  dsimp only [a,b] at hca' hcb'
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetNuclearRankOne -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate
variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

lemma traceNorm_real_smul (r : ℝ) (hr:0 ≤ r) (A : Matrix α β ℂ) :
    WildeQIT.traceNorm (r • A)=r*WildeQIT.traceNorm A := by
  have hg:(r • A)ᴴ*(r • A)=r^2 • (Aᴴ*A) := by
    simp only [Matrix.conjTranspose_smul,star_trivial,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [pow_two]
  rw [WildeQIT.traceNorm,hg,sqrt_smul_sq r hr _ (Matrix.posSemidef_conjTranspose_mul_self A),Matrix.trace_smul]
  change (r • (CFC.sqrt (Aᴴ*A)).trace).re=r*_
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl

def rankOne (u : α→ℂ) (v : β→ℂ) : Matrix α β ℂ := fun i j=>u i*star (v j)

lemma unitary_column_unit (U : Matrix.unitaryGroup α ℂ) (j : α) :
    ∑i,star ((U:Matrix α α ℂ) i j)*(U:Matrix α α ℂ) i j=1 := by
  have hh:=congrArg (fun A:Matrix α α ℂ=>A j j) (Unitary.coe_star_mul_self U)
  simpa only [Matrix.mul_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply,Matrix.one_apply_eq] using hh

/-- Square singular-value decomposition in the form needed for a nuclear
norm estimate on a linear map. Zero singular values and empty spaces are allowed. -/
theorem nuclear_rankOne_decomposition (A : Matrix α α ℂ) :
    ∃s:α→ℝ, (∀i,0 ≤ s i) ∧ ∃L R:Matrix.unitaryGroup α ℂ,
      A=∑i,s i • rankOne (fun a=>(L:Matrix α α ℂ) a i) (fun a=>(R:Matrix α α ℂ) a i) ∧
      (∑i,s i)=WildeQIT.traceNorm A := by
  let P:=CFC.sqrt (Aᴴ*A)
  have hP:P.PosSemidef := (CFC.sqrt_nonneg (Aᴴ*A)).posSemidef
  obtain ⟨W,hW⟩:=Nuclear.polar A
  rw [← sqrt_eq_cfc _ (Matrix.posSemidef_conjTranspose_mul_self A)] at hW
  let R:=hP.isHermitian.eigenvectorUnitary
  let L:=W*R
  let s:=hP.isHermitian.eigenvalues
  have hs:∀i,0 ≤ s i := hP.eigenvalues_nonneg
  have hp:P=(R:Matrix α α ℂ)*Matrix.diagonal (fun i=>(s i:ℂ))*(R:Matrix α α ℂ)ᴴ := by
    convert hP.isHermitian.spectral_theorem using 1 <;>
      simp only [R,s,Unitary.conjStarAlgAut_apply,Function.comp_def,Matrix.star_eq_conjTranspose]
    rfl
  have hA:A=(L:Matrix α α ℂ)*Matrix.diagonal (fun i=>(s i:ℂ))*(R:Matrix α α ℂ)ᴴ := by
    rw [← hW]
    change (W:Matrix α α ℂ)*P=_
    rw [hp]
    simp only [L,Submonoid.coe_mul,Matrix.mul_assoc]
  refine ⟨s,hs,L,R,?_,?_⟩
  · rw [hA]
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,Matrix.sum_apply,Matrix.smul_apply,rankOne,
      Complex.real_smul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · have hh:=congrArg Complex.re hP.isHermitian.trace_eq_sum_eigenvalues
    change (∑i,s i)=P.trace.re
    simpa only [Complex.re_sum,RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_re] using hh.symm

/-- To bound a linear map for the exact public nuclear norm, it suffices to
bound its values on unit rank-one matrices. -/
theorem nuclear_map_bound (T : Matrix α α ℂ →ₗ[ℝ] Matrix β γ ℂ) (C : ℝ)
    (hC:0 ≤ C)
    (hT:∀u v:α→ℂ, (∑i,star (u i)*u i)=1 → (∑i,star (v i)*v i)=1 →
      WildeQIT.traceNorm (T (rankOne u v)) ≤ C) (A : Matrix α α ℂ) :
    WildeQIT.traceNorm (T A) ≤ C*WildeQIT.traceNorm A := by
  obtain ⟨s,hs,L,R,hA,htrace⟩:=nuclear_rankOne_decomposition A
  conv_lhs => rw [hA,map_sum]
  calc
    _ ≤ ∑i,WildeQIT.traceNorm (T (s i • rankOne
        (fun a=>(L:Matrix α α ℂ) a i) (fun a=>(R:Matrix α α ℂ) a i))) := traceNorm_sum_le _ _
    _ = ∑i,s i*WildeQIT.traceNorm (T (rankOne
        (fun a=>(L:Matrix α α ℂ) a i) (fun a=>(R:Matrix α α ℂ) a i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul,traceNorm_real_smul _ (hs i)]
    _ ≤ ∑i,s i*C := Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left
      (hT _ _ (unitary_column_unit L i) (unitary_column_unit R i)) (hs i))
    _ = C*WildeQIT.traceNorm A := by rw [← Finset.sum_mul,htrace,mul_comm]

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetTraceBudget -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker
variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype E] [DecidableEq E]

def appendReference (v : X→ℂ) : Matrix E (E×X) ℂ := fun e er=>if e=er.1 then star (v er.2) else 0

lemma appendReference_coisometry (v : X→ℂ) (hv:(∑i,star (v i)*v i)=1) :
    appendReference (E:=E) v*(appendReference (E:=E) v)ᴴ=(1:Matrix E E ℂ) := by
  ext e f
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,appendReference,Fintype.sum_prod_type]
  by_cases h:e=f
  · subst f
    rw [Finset.sum_eq_single e]
    · simpa only [if_true,star_star,Matrix.one_apply_eq] using hv
    · intro b hb hbe
      simp [Ne.symm hbe]
    · simp
  · simp [h,Ne.symm h,Matrix.one_apply]

def vectorCoefficient (w : Y×E→ℂ) : Matrix Y E ℂ := fun y e=>w (y,e)

lemma hsNorm_vectorCoefficient_isometry (V : Matrix (Y×E) X ℂ) (hV:Vᴴ*V=1)
    (u : X→ℂ) (hu:(∑i,star (u i)*u i)=1) : hsNorm (vectorCoefficient (V*ᵥu))=1 := by
  let A : Matrix X Unit ℂ:=fun i _=>u i
  have ha:hsNorm A=1 := by
    have hg:Aᴴ*A=(1:Matrix Unit Unit ℂ) := by
      ext i j
      simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,A,Matrix.one_apply_eq,
        Subsingleton.elim i j,ite_true] using hu
    rw [hsNorm,hg]
    simp
  have hv:=hsNorm_isometry_left V hV A
  have he:hsNorm (vectorCoefficient (V*ᵥu))=hsNorm (coefficient (V*A)) := by
    unfold hsNorm
    congr 2
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,coefficient,
      vectorCoefficient,Fintype.sum_prod_type,Fintype.sum_unique,A,Matrix.mulVec,dotProduct]
    try simp only [Matrix.mul_apply,Matrix.conjTranspose_apply]
  rw [he,hsNorm_coefficient,hv,ha]

lemma mul_rankOne {R : Type} (V : Matrix Y X ℂ) (u : X→ℂ) (v : R→ℂ) :
    V*rankOne u v=rankOne (V*ᵥu) v := by
  ext y r
  simp only [Matrix.mul_apply,rankOne,Matrix.mulVec,dotProduct,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma coefficient_filtered_rankOne (G : Matrix E E ℂ) (V : Matrix (Y×E) X ℂ) (u v : X→ℂ) :
    coefficient (((1:Matrix Y Y ℂ) ⊗ₖ G)*V*rankOne u v)=
      vectorCoefficient (V*ᵥu)*Gᵀ*appendReference v := by
  rw [Matrix.mul_assoc,mul_rankOne,mul_rankOne]
  ext y er
  rcases er with ⟨e,r⟩
  simp only [coefficient,rankOne,Matrix.mulVec,dotProduct,Matrix.kronecker_apply,Matrix.one_apply,
    Fintype.sum_prod_type,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [Matrix.mul_apply,appendReference,Matrix.transpose_apply,vectorCoefficient,mul_ite,mul_zero,
    Fintype.sum_prod_type,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,if_true,one_mul,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def filteredCoefficientMap (G : Matrix E E ℂ) (V : Matrix (Y×E) X ℂ) :
    Matrix X X ℂ →ₗ[ℝ] Matrix Y (E×X) ℂ where
  toFun A:=coefficient (((1:Matrix Y Y ℂ) ⊗ₖ G)*V*A)
  map_add' A B:=by rw [Matrix.mul_add,coefficient_add]
  map_smul' r A:=by rw [Matrix.mul_smul,coefficient_smul];rfl

lemma hsNorm_transpose (G : Matrix E E ℂ) : hsNorm Gᵀ=hsNorm G := by
  unfold hsNorm
  congr 2
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- Source Eq(9), first step: the isometry and the final effect give an
actual rectangular nuclear-norm bound, proved by a finite singular-value
decomposition and Schatten Holder. -/
theorem filtered_trace_budget (F : Matrix E E ℂ) (hF:F.PosSemidef)
    (V : Matrix (Y×E) X ℂ) (hV:Vᴴ*V=1) (A : Matrix X X ℂ) :
    (CFC.sqrt (ptraceRight
      ((((1:Matrix Y Y ℂ) ⊗ₖ CFC.sqrt F)*V*A)*
       (((1:Matrix Y Y ℂ) ⊗ₖ CFC.sqrt F)*V*A)ᴴ))).trace.re ≤
      Real.sqrt F.trace.re*WildeQIT.traceNorm A := by
  rw [← coefficient_traceNorm]
  apply nuclear_map_bound (filteredCoefficientMap (CFC.sqrt F) V) _ (Real.sqrt_nonneg _)
  intro u v hu hv
  change WildeQIT.traceNorm (coefficient (((1:Matrix Y Y ℂ) ⊗ₖ CFC.sqrt F)*V*rankOne u v)) ≤ _
  rw [coefficient_filtered_rankOne,
    traceNorm_mul_coisometry _ _ (appendReference_coisometry v hv)]
  have hh:=traceNorm_mul_le_hs (vectorCoefficient (V*ᵥu)) (CFC.sqrt F)ᵀ
  rw [hsNorm_vectorCoefficient_isometry V hV u hu,one_mul,hsNorm_transpose,hsNorm_sqrt F hF] at hh
  exact hh

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetTheorem7Lower -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker
variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype E] [DecidableEq E]

/-- Eq(7) and Eq(8) instantiated on the actual public finite ensemble,
isometry, and both actual decoder POVMs. No extra regularity hypothesis. -/
theorem theorem7_fidelity_lower (A B : ℕ) (hA:0<A)
    (ξ : Fin A→Matrix X X ℂ) (hξ:∀x,(ξ x).PosSemidef) (hξ1:∑x,(ξ x).trace=1)
    (V : Matrix (Y×E) X ℂ) (hV:Vᴴ*V=1) (f : Fin A→Fin B)
    (Ex : Fin A→Matrix X X ℂ) (hEx:IsPOVM Ex)
    (Fz : Fin B→Matrix E E ℂ) (hFz:IsPOVM Fz)
    (ρ : Fin A→Matrix Y Y ℂ) (hρ:∀x,IsDensity (ρ x)) :
    let p:ℝ:=1/(A:ℝ)
    let c:=fun x=>clipCoefficient p (ξ x).trace.re
    let τ:=blockMatrix (fun x=>p • ρ x)
    let Ω:=blockMatrix (fun x=>ptraceRight (V*ξ x*Vᴴ))
    let K:=fun x=>((1:Matrix Y Y ℂ) ⊗ₖ CFC.sqrt (Fz (f x)))*V*CFC.sqrt (Ex x)*CFC.sqrt (c x • ξ x)
    let ζ:=blockMatrix (fun x=>ptraceRight (K x*(K x)ᴴ))
    let e₀:ℝ:=1-(∑x,(Ex x*ξ x).trace).re
    let e₁:ℝ:=1-(∑x,(((1:Matrix Y Y ℂ) ⊗ₖ Fz (f x))*(V*ξ x*Vᴴ)).trace).re
    1-(3/2:ℝ)*tdist Ω τ-Real.sqrt e₀-Real.sqrt e₁ ≤ rootFidelity τ ζ := by
  dsimp only
  let p:ℝ:=1/(A:ℝ)
  have hAr:0<(A:ℝ) := by exact_mod_cast hA
  have hp:0<p := one_div_pos.mpr hAr
  let τb:=fun x:Fin A=>p • ρ x
  let Ωb:=fun x:Fin A=>ptraceRight (V*ξ x*Vᴴ)
  let c:=fun x:Fin A=>clipCoefficient p (ξ x).trace.re
  let ξc:=fun x:Fin A=>c x • ξ x
  let F:=fun x:Fin A=>(1:Matrix Y Y ℂ) ⊗ₖ Fz (f x)
  have hc:∀x,0 ≤ c x := fun x=>clipCoefficient_nonneg p _ hp (CFCBasics.psd_re (hξ x))
  have hξc:∀x,(ξc x).PosSemidef := fun x=>(hξ x).smul (hc x)
  have hτ:∀x,(τb x).PosSemidef := fun x=>(hρ x).1.smul hp.le
  have hτtr:∀x,(τb x).trace=(p:ℂ) := by
    intro x
    simp only [τb,Matrix.trace_smul,(hρ x).2,Complex.real_smul,mul_one]
  have hτr:∀x,(τb x).trace.re=p := fun x=>by rw [hτtr];rfl
  have hτsum:∑x,(τb x).trace=1 := by
    simp only [hτtr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change (A:ℂ)*(p:ℂ)=1
    rw [← Complex.ofReal_natCast,← Complex.ofReal_mul]
    norm_cast
    dsimp [p]
    exact mul_one_div_cancel (ne_of_gt hAr)
  have hτD:=blockMatrix_density τb hτ hτsum
  have hΩD:=blockMatrix_isometry_marginal_density ξ hξ hξ1 V hV
  have hΩ:∀x,(Ωb x).PosSemidef := fun x=>QuantumRankProof.ptraceRight_posSemidef _
    ((hξ x).mul_mul_conjTranspose_same V)
  have hΩtr:∀x,(Ωb x).trace=(ξ x).trace := fun x=>by
    dsimp only [Ωb]
    rw [QuantumRankProof.trace_ptraceRight,trace_isometry V hV]
  have hclip:=clipped_fidelity_bound p hp τb Ωb hτ hΩ hτr hτD hΩD
  have hΩclip:∀x,ptraceRight (V*ξc x*Vᴴ)=c x • Ωb x := by
    intro x
    dsimp only [ξc]
    rw [Matrix.mul_smul,Matrix.smul_mul,ptraceRight_smul]
  have hclip':1-(3/2:ℝ)*tdist (blockMatrix Ωb) (blockMatrix τb) ≤
      rootFidelity (blockMatrix τb) (blockMatrix (fun x=>ptraceRight (V*ξc x*Vᴴ))) := by
    convert hclip using 1
    congr 2
    funext x
    rw [hΩclip,hΩtr]
  have hF:∀x,(F x).PosSemidef := fun x=>Matrix.PosSemidef.one.kronecker (hFz.1 (f x))
  have hcF:∀x,(1-F x).PosSemidef := fun x=>output_effect_compl _
    (povm_compl_posSemidef Fz hFz (f x))
  have hcEx:∀x,(1-Ex x).PosSemidef := fun x=>povm_compl_posSemidef Ex hEx x
  have he₀:(∑x,((1-Ex x)*ξc x).trace.re) ≤ 1-(∑x,(Ex x*ξ x).trace).re := by
    rw [← failure_sum_eq ξ Ex hξ1]
    exact Finset.sum_le_sum (fun x _=>clipping_failure_le p hp (ξ x) (Ex x) (hξ x) (hcEx x))
  have he₁:(∑x,((1-F x)*(V*ξc x*Vᴴ)).trace.re) ≤ 1-(∑x,(F x*(V*ξ x*Vᴴ)).trace).re := by
    have hsum:∑x,(V*ξ x*Vᴴ).trace=1 := by simpa only [trace_isometry V hV] using hξ1
    rw [← failure_sum_eq (fun x=>V*ξ x*Vᴴ) F hsum]
    apply Finset.sum_le_sum
    intro x hx
    have hh:=clipping_failure_le p hp (V*ξ x*Vᴴ) (F x)
      ((hξ x).mul_mul_conjTranspose_same V) (hcF x)
    rw [trace_isometry V hV] at hh
    simpa only [ξc,c,Matrix.mul_smul,Matrix.smul_mul] using hh
  have hτsumr:∑x,(τb x).trace.re=1 := by rw [← Complex.re_sum,hτsum];rfl
  have hfinal:=filtered_ensemble_fidelity τb hτ hτsumr ξc hξc V hV Ex hEx.1 hcEx F hF hcF _ _ he₀ he₁
  dsimp only at hfinal
  simp only [F,output_effect_sqrt _ (hFz.1 _)] at hfinal
  linarith

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetBalancedDecoder -/

set_option autoImplicit false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker

lemma sum_balanced_fibres (A B : ℕ) (hB:0<B) (f : Fin A→Fin B)
    (hf:∀z,(Finset.univ.filter (fun x=>f x=z)).card*B=A) (w : Fin B→ℝ) :
    (∑x,w (f x))=(A:ℝ)/(B:ℝ)*∑z,w z := by
  have hsum:(∑x,w (f x))=∑z,((Finset.univ.filter (fun x=>f x=z)).card:ℝ)*w z := by
    calc
      _ = ∑x:Fin A,∑z:Fin B,if f x=z then w z else 0 := by simp
      _ = ∑z:Fin B,∑x:Fin A,if f x=z then w z else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [← Finset.sum_filter]
        simp
  rw [hsum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  have hb:(B:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  apply (eq_div_iff hb).mpr
  exact_mod_cast hf z

lemma povm_trace_sum {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]
    (E : ι→Matrix α α ℂ) (hE:IsPOVM E) :
    (∑i,(E i).trace.re)=(Fintype.card α:ℝ) := by
  rw [← Complex.re_sum,← Matrix.trace_sum,hE.2,Matrix.trace_one]
  simp

lemma decoder_trace_cauchy {X E : Type} [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    (A B : ℕ) (hB:0<B) (f : Fin A→Fin B)
    (hf:∀z,(Finset.univ.filter (fun x=>f x=z)).card*B=A)
    (Ex : Fin A→Matrix X X ℂ) (hEx:IsPOVM Ex)
    (Fz : Fin B→Matrix E E ℂ) (hFz:IsPOVM Fz) :
    (∑x,Real.sqrt (Ex x).trace.re*Real.sqrt (Fz (f x)).trace.re) ≤
      Real.sqrt (Fintype.card X)*Real.sqrt ((A:ℝ)/(B:ℝ)*Fintype.card E) := by
  have hh:=Real.sum_sqrt_mul_sqrt_le (Finset.univ:Finset (Fin A))
    (fun x=>CFCBasics.psd_re (hEx.1 x)) (fun x=>CFCBasics.psd_re (hFz.1 (f x)))
  rw [povm_trace_sum Ex hEx,
    sum_balanced_fibres A B hB f hf (fun z=>(Fz z).trace.re),povm_trace_sum Fz hFz] at hh
  exact hh

lemma dimension_budget_scaling (A B : ℝ) (M : ℝ) (d₀ d₁ : ℝ)
    (hA:0<A) (hB:0<B) (hM:0<M) (hd₀:0 ≤ d₀) (hd₁:0 ≤ d₁) :
    Real.sqrt (A*B*M)*(1/A/Real.sqrt M)*
      (Real.sqrt d₀*Real.sqrt (A/B*d₁))=Real.sqrt (d₀*d₁) := by
  rw [Real.sqrt_mul (mul_nonneg hA.le hB.le),Real.sqrt_mul hA.le,
    Real.sqrt_mul (div_nonneg hA.le hB.le),Real.sqrt_div hA.le,Real.sqrt_mul hd₀]
  have hsA:Real.sqrt A*Real.sqrt A=A := Real.mul_self_sqrt hA.le
  have hsB:Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  have hsM:Real.sqrt M ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hM)
  field_simp
  rw [Real.sq_sqrt hA.le]

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetTheorem7Upper -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SpaceReset.Hardness.FidelityProof
open Matrix Finset
open scoped ComplexOrder MatrixOrder ComplexConjugate Kronecker
variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype E] [DecidableEq E]

lemma real_smul_eq_complex (r : ℝ) (A : Matrix X Y ℂ) : r • A=(r:ℂ) • A := by
  ext i j
  exact Complex.real_smul

lemma sqrt_quotient_pair (p M : ℝ) (hp:0 ≤ p) (hM:0<M) :
    Real.sqrt (p/M)*Real.sqrt p=p/Real.sqrt M := by
  rw [Real.sqrt_div hp]
  have hh:Real.sqrt M ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hM)
  rw [div_mul_eq_mul_div,Real.mul_self_sqrt hp]

/-- The output filtered ensemble has the exact two-endpoint dimension
budget. The balanced decoder fibres are used only in the final finite sum. -/
theorem theorem7_fidelity_dimension (A B : ℕ) (hA:0<A) (hB:0<B) (M : ℝ) (hM:0<M)
    (ξ : Fin A→Matrix X X ℂ) (hξ:∀x,(ξ x).PosSemidef)
    (V : Matrix (Y×E) X ℂ) (hV:Vᴴ*V=1) (f : Fin A→Fin B)
    (hf:∀z,(Finset.univ.filter (fun x=>f x=z)).card*B=A)
    (Ex : Fin A→Matrix X X ℂ) (hEx:IsPOVM Ex)
    (Fz : Fin B→Matrix E E ℂ) (hFz:IsPOVM Fz)
    (ρ : Fin A→Matrix Y Y ℂ) (hρ:∀x,IsDensity (ρ x))
    (hρM:∀x,ρ x ≤ ((1/M:ℝ):ℂ) • (1:Matrix Y Y ℂ)) :
    let p:ℝ:=1/(A:ℝ)
    let c:=fun x=>clipCoefficient p (ξ x).trace.re
    let τ:=blockMatrix (fun x=>p • ρ x)
    let K:=fun x=>((1:Matrix Y Y ℂ) ⊗ₖ CFC.sqrt (Fz (f x)))*V*CFC.sqrt (Ex x)*CFC.sqrt (c x • ξ x)
    let ζ:=blockMatrix (fun x=>ptraceRight (K x*(K x)ᴴ))
    Real.sqrt ((A:ℝ)*B*M)*rootFidelity τ ζ ≤ Real.sqrt ((Fintype.card X:ℝ)*Fintype.card E) := by
  dsimp only
  let p:ℝ:=1/(A:ℝ)
  have hAr:0<(A:ℝ) := by exact_mod_cast hA
  have hBr:0<(B:ℝ) := by exact_mod_cast hB
  have hp:0<p := one_div_pos.mpr hAr
  let c:=fun x:Fin A=>clipCoefficient p (ξ x).trace.re
  let ξc:=fun x:Fin A=>c x • ξ x
  let K:=fun x:Fin A=>((1:Matrix Y Y ℂ) ⊗ₖ CFC.sqrt (Fz (f x)))*V*CFC.sqrt (Ex x)*CFC.sqrt (ξc x)
  let ζb:=fun x:Fin A=>ptraceRight (K x*(K x)ᴴ)
  have hξc:∀x,(ξc x).PosSemidef := fun x=>(hξ x).smul
    (clipCoefficient_nonneg p _ hp (CFCBasics.psd_re (hξ x)))
  have htr:∀x,(ξc x).trace.re ≤ p := by
    intro x
    simp only [ξc,Matrix.trace_smul,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    exact clipCoefficient_trace_le p _ hp (CFCBasics.psd_re (hξ x))
  have hζ:∀x,(ζb x).PosSemidef := fun x=>QuantumRankProof.ptraceRight_posSemidef _
    (Matrix.posSemidef_self_mul_conjTranspose _)
  have hτ:∀x,(p • ρ x).PosSemidef := fun x=>(hρ x).1.smul hp.le
  have hbudget:∀x,(CFC.sqrt (ζb x)).trace.re ≤
      Real.sqrt (Fz (f x)).trace.re*Real.sqrt (Ex x).trace.re*Real.sqrt p := by
    intro x
    have ht:=filtered_trace_budget (Fz (f x)) (hFz.1 _) V hV (CFC.sqrt (Ex x)*CFC.sqrt (ξc x))
    have ht':(CFC.sqrt (ζb x)).trace.re ≤ Real.sqrt (Fz (f x)).trace.re*
        WildeQIT.traceNorm (CFC.sqrt (Ex x)*CFC.sqrt (ξc x)) := by
      simpa only [ζb,K,Matrix.mul_assoc] using ht
    have hh:=traceNorm_mul_le_hs (CFC.sqrt (Ex x)) (CFC.sqrt (ξc x))
    rw [hsNorm_sqrt _ (hEx.1 x),hsNorm_sqrt _ (hξc x)] at hh
    have hp':Real.sqrt (ξc x).trace.re ≤ Real.sqrt p := Real.sqrt_le_sqrt (htr x)
    have hh':WildeQIT.traceNorm (CFC.sqrt (Ex x)*CFC.sqrt (ξc x)) ≤
        Real.sqrt (Ex x).trace.re*Real.sqrt p := hh.trans
      (mul_le_mul_of_nonneg_left hp' (Real.sqrt_nonneg _))
    exact ht'.trans (by nlinarith [mul_le_mul_of_nonneg_left hh' (Real.sqrt_nonneg (Fz (f x)).trace.re)])
  have hfid:∀x,rootFidelity (p • ρ x) (ζb x) ≤
      (p/Real.sqrt M)*(Real.sqrt (Ex x).trace.re*Real.sqrt (Fz (f x)).trace.re) := by
    intro x
    have hbound:((Real.sqrt (p/M))^2 • (1:Matrix Y Y ℂ)-p • ρ x).PosSemidef := by
      rw [Real.sq_sqrt (div_nonneg hp.le hM.le)]
      have hb:=Matrix.le_iff.mp (hρM x)
      rw [← real_smul_eq_complex] at hb
      have hh:=hb.smul hp.le
      simpa only [smul_sub,smul_smul,div_eq_mul_inv,one_mul] using hh
    have hh:=rootFidelity_spectral_upper (p • ρ x) (ζb x) (hτ x) (hζ x)
      (Real.sqrt (p/M)) (Real.sqrt_nonneg _) hbound
    have he:Real.sqrt (p/M)*(Real.sqrt (Fz (f x)).trace.re*Real.sqrt (Ex x).trace.re*Real.sqrt p)=
        (p/Real.sqrt M)*(Real.sqrt (Ex x).trace.re*Real.sqrt (Fz (f x)).trace.re) := by
      rw [show Real.sqrt (p/M)*(Real.sqrt (Fz (f x)).trace.re*Real.sqrt (Ex x).trace.re*Real.sqrt p)=
        (Real.sqrt (p/M)*Real.sqrt p)*(Real.sqrt (Ex x).trace.re*Real.sqrt (Fz (f x)).trace.re) by ring,
        sqrt_quotient_pair p M hp.le hM]
    exact hh.trans ((mul_le_mul_of_nonneg_left (hbudget x) (Real.sqrt_nonneg _)).trans_eq he)
  have hsum:=Finset.sum_le_sum (fun x (_:x∈(Finset.univ:Finset (Fin A)))=>hfid x)
  rw [← Finset.mul_sum] at hsum
  have hcs:=decoder_trace_cauchy A B hB f hf Ex hEx Fz hFz
  have hscale:=dimension_budget_scaling (A:ℝ) B M (Fintype.card X) (Fintype.card E)
    hAr hBr hM (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfinal:=mul_le_mul_of_nonneg_left
    (hsum.trans (mul_le_mul_of_nonneg_left hcs (div_nonneg hp.le (Real.sqrt_nonneg _))))
    (Real.sqrt_nonneg ((A:ℝ)*B*M))
  rw [← mul_assoc,hscale] at hfinal
  rw [rootFidelity_blockMatrix _ _ hτ hζ]
  exact hfinal

end SpaceReset.Hardness.FidelityProof

/- Module SpaceResetTwoEndpoints -/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

namespace SpaceReset.Hardness.FidelityProof

/-- Theorem 7 (Two endpoints with different decoded labels), §2.3, pp. 13–14, eq. (6). -/
theorem theorem_7 {E₀ E₁ Y : Type} [Fintype E₀] [DecidableEq E₀] [Fintype E₁] [DecidableEq E₁]
    [Fintype Y] [DecidableEq Y] (A B : ℕ) (M : ℝ) (hM : 0 < M)
    (ξ : Fin A → Matrix E₀ E₀ ℂ) (hξ : ∀ x, (ξ x).PosSemidef) (hξ1 : ∑ x, (ξ x).trace = 1)
    (V : Matrix (Y × E₁) E₀ ℂ) (hV : Vᴴ * V = 1)
    (f : Fin A → Fin B) (hf : ∀ z : Fin B, (Finset.univ.filter (fun x => f x = z)).card * B = A)
    (Ex : Fin A → Matrix E₀ E₀ ℂ) (hEx : IsPOVM Ex)
    (Fz : Fin B → Matrix E₁ E₁ ℂ) (hFz : IsPOVM Fz)
    (ρ : Fin A → Matrix Y Y ℂ) (hρ : ∀ x, IsDensity (ρ x))
    (hρM : ∀ x, ρ x ≤ ((1 / M : ℝ) : ℂ) • (1 : Matrix Y Y ℂ)) :
    let e₀ : ℝ := 1 - (∑ x, (Ex x * ξ x).trace).re
    let e₁ : ℝ := 1 - (∑ x, (((1 : Matrix Y Y ℂ) ⊗ₖ Fz (f x)) * (V * ξ x * Vᴴ)).trace).re
    let Ω : Matrix (Fin A × Y) (Fin A × Y) ℂ :=
      fun p p' => if p.1 = p'.1 then ptraceRight (V * ξ p.1 * Vᴴ) p.2 p'.2 else 0
    let τ : Matrix (Fin A × Y) (Fin A × Y) ℂ :=
      fun p p' => if p.1 = p'.1 then ((1 : ℂ) / (A : ℂ)) * ρ p.1 p.2 p'.2 else 0
    let δ : ℝ := WildeQIT.traceNorm (Ω - τ) / 2
    Real.sqrt (Fintype.card E₀ * Fintype.card E₁) ≥
      Real.sqrt (A * B * M) * max 0 (1 - (3 / 2) * δ - Real.sqrt e₀ - Real.sqrt e₁) := by
  have hA:0<A := by
    by_contra hh
    have hz:A=0 := by omega
    subst A
    simp at hξ1
  have hB:0<B := by have hb:=(f ⟨0,hA⟩).isLt;omega
  dsimp only
  have hl:=theorem7_fidelity_lower A B hA ξ hξ hξ1 V hV f Ex hEx Fz hFz ρ hρ
  have hu:=theorem7_fidelity_dimension A B hA hB M hM ξ hξ V hV f hf Ex hEx Fz hFz ρ hρ hρM
  dsimp only at hl hu
  have hτ:blockMatrix (fun x:Fin A=>(1/(A:ℝ)) • ρ x)=
      (fun p p':Fin A×Y=>if p.1=p'.1 then ((1:ℂ)/(A:ℂ))*ρ p.1 p.2 p'.2 else 0) := by
    ext p q
    by_cases h:p.1=q.1
    · simp [blockMatrix,h,Matrix.smul_apply,Complex.real_smul,Complex.ofReal_div]
    · simp [blockMatrix,h]
  rw [hτ] at hl hu
  have hh:Real.sqrt ((A:ℝ)*B*M)*
      (1-(3/2:ℝ)*tdist
        (blockMatrix (fun x=>ptraceRight (V*ξ x*Vᴴ)))
        (fun p p':Fin A×Y=>if p.1=p'.1 then ((1:ℂ)/(A:ℂ))*ρ p.1 p.2 p'.2 else 0)-
        Real.sqrt (1-(∑x,(Ex x*ξ x).trace).re)-
        Real.sqrt (1-(∑x,(((1:Matrix Y Y ℂ) ⊗ₖ Fz (f x))*(V*ξ x*Vᴴ)).trace).re)) ≤
      Real.sqrt ((Fintype.card E₀:ℝ)*Fintype.card E₁) :=
    (mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg _)).trans hu
  change Real.sqrt ((Fintype.card E₀:ℝ)*Fintype.card E₁) ≥
    Real.sqrt ((A:ℝ)*B*M)*max 0 _
  rw [mul_max_of_nonneg _ _ (Real.sqrt_nonneg _),mul_zero]
  exact max_le (Real.sqrt_nonneg _) hh


end SpaceReset.Hardness.FidelityProof

open SpaceReset.Hardness
open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

theorem solution {E₀ E₁ Y : Type} [Fintype E₀] [DecidableEq E₀] [Fintype E₁] [DecidableEq E₁]
    [Fintype Y] [DecidableEq Y] (A B : ℕ) (M : ℝ) (hM : 0 < M)
    (ξ : Fin A → Matrix E₀ E₀ ℂ) (hξ : ∀ x, (ξ x).PosSemidef) (hξ1 : ∑ x, (ξ x).trace = 1)
    (V : Matrix (Y × E₁) E₀ ℂ) (hV : Vᴴ * V = 1)
    (f : Fin A → Fin B) (hf : ∀ z : Fin B, (Finset.univ.filter (fun x => f x = z)).card * B = A)
    (Ex : Fin A → Matrix E₀ E₀ ℂ) (hEx : IsPOVM Ex)
    (Fz : Fin B → Matrix E₁ E₁ ℂ) (hFz : IsPOVM Fz)
    (ρ : Fin A → Matrix Y Y ℂ) (hρ : ∀ x, IsDensity (ρ x))
    (hρM : ∀ x, ρ x ≤ ((1 / M : ℝ) : ℂ) • (1 : Matrix Y Y ℂ)) :
    let e₀ : ℝ := 1 - (∑ x, (Ex x * ξ x).trace).re
    let e₁ : ℝ := 1 - (∑ x, (((1 : Matrix Y Y ℂ) ⊗ₖ Fz (f x)) * (V * ξ x * Vᴴ)).trace).re
    let Ω : Matrix (Fin A × Y) (Fin A × Y) ℂ :=
      fun p p' => if p.1 = p'.1 then ptraceRight (V * ξ p.1 * Vᴴ) p.2 p'.2 else 0
    let τ : Matrix (Fin A × Y) (Fin A × Y) ℂ :=
      fun p p' => if p.1 = p'.1 then ((1 : ℂ) / (A : ℂ)) * ρ p.1 p.2 p'.2 else 0
    let δ : ℝ := WildeQIT.traceNorm (Ω - τ) / 2
    Real.sqrt (Fintype.card E₀ * Fintype.card E₁) ≥
      Real.sqrt (A * B * M) * max 0 (1 - (3 / 2) * δ - Real.sqrt e₀ - Real.sqrt e₁) :=
  FidelityProof.theorem_7 A B M hM ξ hξ hξ1 V hV f hf Ex hEx Fz hFz ρ hρ hρM
