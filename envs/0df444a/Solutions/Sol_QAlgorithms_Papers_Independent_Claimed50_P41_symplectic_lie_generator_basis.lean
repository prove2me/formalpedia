-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_lie_generator_basis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:44:32.754149+00:00
-- url     : https://prove2.me/submissions/d989d93d-581e-4a65-92d0-70909118aa56

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace X4LieGen

open QAlgorithms.Papers.Independent.Claimed50.P41 Matrix

variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Phase n) (Phase n) ℝ

lemma sigma_transpose : (sigma n).transpose = -sigma n := by
  unfold sigma
  rw [Matrix.fromBlocks_transpose]
  simp [Matrix.fromBlocks_neg]

lemma sigma_mul_sigma : sigma n * sigma n = -1 := by
  unfold sigma
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_neg, ← Matrix.fromBlocks_one]

lemma sigma_antisymm (u v : Phase n) : sigma n u v = - sigma n v u := by
  have := congrFun (congrFun (sigma_transpose (n := n)) v) u
  simpa [Matrix.transpose_apply] using this

lemma cx_mul {a b c : Type*} [Fintype b] (X : Matrix a b ℝ) (Y : Matrix b c ℝ) :
    complexify (X * Y) = complexify X * complexify Y := by
  ext i j; simp [complexify, Matrix.mul_apply]

lemma cx_add {a b : Type*} (X Y : Matrix a b ℝ) : complexify (X + Y) = complexify X + complexify Y := by
  ext i j; simp [complexify]

lemma cx_sub {a b : Type*} (X Y : Matrix a b ℝ) : complexify (X - Y) = complexify X - complexify Y := by
  ext i j; simp [complexify]

lemma cx_smul {a b : Type*} (r : ℝ) (X : Matrix a b ℝ) : complexify (r • X) = (r : ℂ) • complexify X := by
  ext i j; simp [complexify]

lemma cx_isSymm {a : Type*} {X : Matrix a a ℝ} (h : X.IsSymm) : (complexify X).IsSymm := by
  ext i j; simp [complexify]; exact congrFun (congrFun h i) j ▸ rfl

/-- generator as sigma times symmetric unit matrix -/
def Q (a b : Phase n) : Mat n := Matrix.single b a 1 + Matrix.single a b 1

lemma Q_symm (a b : Phase n) : (Q a b).IsSymm := by
  unfold Q Matrix.IsSymm
  rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single, add_comm]

lemma R_eq (a b : Phase n) : realGenerator a b = sigma n * Q a b := by
  ext c d
  simp only [realGenerator, Q, Matrix.mul_add, Matrix.add_apply, Matrix.mul_apply, Matrix.single_apply]
  simp only [ite_and, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma sR (a b : Phase n) : sigma n * realGenerator a b = - Q a b := by
  rw [R_eq, ← Matrix.mul_assoc, sigma_mul_sigma, Matrix.neg_mul, Matrix.one_mul]

/-- the real symplectic Lie algebra -/
def spAlg (n : ℕ) : Submodule ℝ (Mat n) where
  carrier := {M | (sigma n * M).IsSymm ∧ (M * sigma n).IsSymm}
  add_mem' := by
    rintro A B ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [Matrix.mul_add]; exact h1.add h3, by rw [Matrix.add_mul]; exact h2.add h4⟩
  zero_mem' := by simp [Matrix.IsSymm]
  smul_mem' := by
    rintro c A ⟨h1, h2⟩
    exact ⟨by rw [Matrix.mul_smul]; exact h1.smul c, by rw [Matrix.smul_mul]; exact h2.smul c⟩

lemma R_mem (a b : Phase n) : realGenerator a b ∈ spAlg n := by
  refine ⟨?_, ?_⟩
  · rw [sR]; exact (Q_symm a b).neg
  · rw [R_eq]
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, sigma_transpose, (Q_symm a b).eq]
    simp [Matrix.mul_assoc]

lemma span_le : Submodule.span ℝ (Set.range (fun p : Phase n × Phase n => realGenerator p.1 p.2)) ≤ spAlg n := by
  rw [Submodule.span_le]; rintro _ ⟨p, rfl⟩; exact R_mem _ _

lemma good_of_mem {M : Mat n} (h : M ∈ spAlg n) :
    (∀ c d, star ((Complex.I • complexify M) c d) = -(Complex.I • complexify M) c d) ∧
    (complexify (sigma n) * (Complex.I • complexify M)).IsSymm ∧
    ((Complex.I • complexify M) * complexify (sigma n)).IsSymm := by
  refine ⟨?_, ?_, ?_⟩
  · intro c d; simp [complexify, Complex.ext_iff]
  · rw [Matrix.mul_smul, ← cx_mul]; exact (cx_isSymm h.1).smul _
  · rw [Matrix.smul_mul, ← cx_mul]; exact (cx_isSymm h.2).smul _


lemma pn_inj : Function.Injective (phaseNumber (n := n)) := by
  intro x y h
  rcases x with i | i <;> rcases y with j | j <;> simp [phaseNumber] at h
  · exact congrArg _ (Fin.ext h)
  · have := i.isLt; omega
  · have := j.isLt; omega
  · exact congrArg _ (Fin.ext h)

abbrev Idx (n : ℕ) := {p : Phase n × Phase n // phaseNumber p.1 ≤ phaseNumber p.2}

lemma Q_apply_idx (p i : Idx n) : Q p.val.1 p.val.2 i.val.1 i.val.2 = if p = i then
    (if i.val.1 = i.val.2 then 2 else 1) else 0 := by
  obtain ⟨⟨a, b⟩, hab⟩ := p
  obtain ⟨⟨c, d⟩, hcd⟩ := i
  dsimp only at hab hcd
  have key : b = c ∧ a = d → a = c ∧ b = d := by
    rintro ⟨rfl, rfl⟩
    have := pn_inj (le_antisymm hab hcd); subst this; exact ⟨rfl, rfl⟩
  simp only [Q, Matrix.add_apply, Matrix.single_apply, Subtype.mk.injEq, Prod.mk.injEq]
  by_cases h : a = c ∧ b = d
  · obtain ⟨rfl, rfl⟩ := h
    by_cases hab' : a = b
    · subst hab'; norm_num
    · simp [hab', Ne.symm hab']
  · have h2 : ¬ (b = c ∧ a = d) := fun h' => h (key h')
    simp only [h, h2, if_false]; norm_num

lemma linIndep : LinearIndependent ℝ (fun p : Idx n => realGenerator p.val.1 p.val.2) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (fun M => (sigma n * M) i.val.1 i.val.2) hg
  simp only [Matrix.mul_sum, Matrix.mul_smul, sR, Matrix.sum_apply, Matrix.smul_apply, Matrix.neg_apply,
    Q_apply_idx, smul_eq_mul, Matrix.mul_zero, Matrix.zero_apply] at h
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (fun h' => absurd hi h')] at h
  simp only [if_true] at h
  split_ifs at h <;> linarith

lemma span_eq : Submodule.span ℝ (Set.range (fun p : Phase n × Phase n => realGenerator p.1 p.2)) =
    Submodule.span ℝ (Set.range (fun p : Idx n => realGenerator p.val.1 p.val.2)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨a, b⟩, rfl⟩
    rcases le_total (phaseNumber a) (phaseNumber b) with h | h
    · exact Submodule.subset_span ⟨⟨(a, b), h⟩, rfl⟩
    · have : realGenerator a b = realGenerator b a := by
        ext c d; simp only [realGenerator]; ring
      simp only; rw [this]
      exact Submodule.subset_span ⟨⟨(b, a), h⟩, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨p, rfl⟩; exact ⟨p.val, rfl⟩

lemma card_idx : Fintype.card (Idx n) = n * (2 * n + 1) := by
  have hb : Function.Bijective (fun p : Idx n => (s(p.val.1, p.val.2) : Sym2 (Phase n))) := by
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
      simp only [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · dsimp only at hab hcd
        have := pn_inj (le_antisymm hab hcd); subst this; rfl
    · intro z
      induction z using Sym2.ind with
      | h a b =>
        rcases le_total (phaseNumber a) (phaseNumber b) with h | h
        · exact ⟨⟨(a, b), h⟩, rfl⟩
        · exact ⟨⟨(b, a), h⟩, Sym2.eq_swap⟩
  rw [Fintype.card_of_bijective hb, Sym2.card]
  simp only [Fintype.card_sum, Fintype.card_fin]
  rw [Nat.choose_two_right]
  have : (n + n + 1) * (n + n + 1 - 1) = 2 * (n * (2 * n + 1)) := by
    rw [show n + n + 1 - 1 = 2 * n by omega]; ring
  rw [this]; omega

lemma finrank_span : Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun p : Phase n × Phase n => realGenerator p.1 p.2))) = n * (2 * n + 1) := by
  rw [span_eq, finrank_span_eq_card linIndep, card_idx]


lemma R_comm (a b c d : Phase n) :
    realGenerator a b * realGenerator c d - realGenerator c d * realGenerator a b =
      sigma n a c • realGenerator b d + sigma n b c • realGenerator a d +
      sigma n a d • realGenerator c b + sigma n b d • realGenerator c a := by
  ext x y
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, realGenerator,
    smul_eq_mul, add_mul, mul_add, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [sigma_antisymm c a, sigma_antisymm d a, sigma_antisymm d b, sigma_antisymm c b]
  split_ifs <;> ring

lemma part5 (a b c d : Phase n) : algebraCommutator (generatorMatrix a b) (generatorMatrix c d) =
      Complex.I • ((sigma n a c : ℂ) • generatorMatrix b d +
        (sigma n b c : ℂ) • generatorMatrix a d + (sigma n a d : ℂ) • generatorMatrix c b +
        (sigma n b d : ℂ) • generatorMatrix c a) := by
  have h := congrArg complexify (R_comm a b c d)
  simp only [cx_sub, cx_add, cx_smul, cx_mul] at h
  unfold algebraCommutator generatorMatrix
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← smul_sub, h, smul_add]
  simp only [Complex.I_mul_I]
  congr 1 <;> [congr 1; skip] <;> [congr 1; skip; skip] <;>
    simp only [neg_smul, one_smul, smul_smul, mul_comm Complex.I, mul_assoc, Complex.I_mul_I, mul_neg, mul_one, neg_one_mul]

lemma char_fwd (J : Matrix (Phase n) (Phase n) ℂ) (h1 : ∀ c d, star (J c d) = -J c d)
    (h2 : (complexify (sigma n) * J).IsSymm) :
    ∃ M ∈ Submodule.span ℝ (Set.range (fun p : Phase n × Phase n => realGenerator p.1 p.2)),
        J = Complex.I • complexify M := by
  set M : Mat n := fun c d => (J c d).im
  have hJ : J = Complex.I • complexify M := by
    ext c d
    have := h1 c d
    simp only [Complex.ext_iff, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.neg_re,
      Complex.neg_im] at this
    simp [Complex.ext_iff, M, complexify]; linarith [this.1]
  refine ⟨M, ?_, hJ⟩
  have hS : (sigma n * M).IsSymm := by
    rw [hJ, Matrix.mul_smul, ← cx_mul] at h2
    ext c d
    have := congrFun (congrFun h2 c) d
    simpa [Matrix.transpose_apply, complexify] using this
  set S : Mat n := -(sigma n * M)
  have hSS : ∀ a b, S a b = S b a := fun a b => by
    simp only [S, Matrix.neg_apply]; rw [← Matrix.transpose_apply (sigma n * M) b a, hS.eq]
  have hM : M = ∑ a, ∑ b, (S a b / 2) • realGenerator a b := by
    have h3 : M = sigma n * S := by
      simp only [S, Matrix.mul_neg, ← Matrix.mul_assoc, sigma_mul_sigma]; simp
    ext c d
    rw [h3]
    simp only [Matrix.sum_apply, Matrix.smul_apply, realGenerator, smul_eq_mul, mul_add, mul_ite,
      mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Matrix.mul_apply]
    rw [Finset.sum_comm (f := fun x y => if x = d then S x y / 2 * sigma n c y else 0)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hSS d x]; ring
  rw [hM]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨(a, b), rfl⟩


lemma sigma_inv : (sigma n)⁻¹ = -sigma n :=
  Matrix.inv_eq_right_inv (by rw [Matrix.mul_neg, sigma_mul_sigma, neg_neg])

lemma sigma_isUnit : IsUnit (sigma n) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_right_inverse (B := -sigma n) (by rw [Matrix.mul_neg, sigma_mul_sigma, neg_neg]))

lemma exp_symp {B : Mat n} (hB : (B * sigma n).IsSymm) : PreservesCanonicalForm (NormedSpace.exp B) := by
  have h1 : sigma n * B.transpose = -(B * sigma n) := by
    have := hB.eq
    rw [Matrix.transpose_mul, sigma_transpose, Matrix.neg_mul] at this
    rw [← this, neg_neg]
  have hB' : B = sigma n * (-B.transpose) * (sigma n)⁻¹ := by
    rw [sigma_inv, Matrix.mul_neg (sigma n) B.transpose, h1, neg_neg, Matrix.mul_neg, Matrix.mul_assoc,
      sigma_mul_sigma]; simp
  have hE : NormedSpace.exp B = sigma n * NormedSpace.exp (-B.transpose) * (sigma n)⁻¹ := by
    conv_lhs => rw [hB']
    exact Matrix.exp_conj _ _ sigma_isUnit
  unfold PreservesCanonicalForm
  rw [← Matrix.exp_transpose, hE, sigma_inv]
  have hinv : NormedSpace.exp (-B.transpose) * NormedSpace.exp B.transpose = 1 := by
    rw [Matrix.exp_neg]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))
  calc sigma n * NormedSpace.exp (-B.transpose) * -sigma n * sigma n * NormedSpace.exp B.transpose
      = sigma n * (NormedSpace.exp (-B.transpose) * NormedSpace.exp B.transpose) := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, sigma_mul_sigma]; simp
    _ = sigma n := by rw [hinv, Matrix.mul_one]

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
lemma exp_cx (A : Mat n) : NormedSpace.exp (complexify A) = complexify (NormedSpace.exp A) := by
  have hf : Continuous (fun X : Mat n => X.map (fun x : ℝ => (x : ℂ))) :=
    Continuous.matrix_map continuous_id Complex.continuous_ofReal
  have := NormedSpace.map_exp (Complex.ofRealHom.mapMatrix : Mat n →+* Matrix (Phase n) (Phase n) ℂ) hf A
  exact this.symm

end X4LieGen

open MeasureTheory
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Claimed50.P41 X4LieGen in
theorem solution (n : ℕ) (_hn : 0 < n) :
    (∀ a b : Phase n, generatorMatrix a b = generatorMatrix b a ∧
      (∀ c d, star (generatorMatrix a b c d) = -generatorMatrix a b c d) ∧
      (complexify (sigma n) * generatorMatrix a b).IsSymm ∧
      (generatorMatrix a b * complexify (sigma n)).IsSymm) ∧
    LinearIndependent ℝ (fun p : {p : Phase n × Phase n // phaseNumber p.1 ≤ phaseNumber p.2} =>
      realGenerator p.val.1 p.val.2) ∧
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun p : Phase n × Phase n => realGenerator p.1 p.2))) = n * (2 * n + 1) ∧
    (∀ J : Matrix (Phase n) (Phase n) ℂ,
      ((∀ c d, star (J c d) = -J c d) ∧
        (complexify (sigma n) * J).IsSymm ∧ (J * complexify (sigma n)).IsSymm) ↔
      ∃ M ∈ Submodule.span ℝ (Set.range (fun p : Phase n × Phase n => realGenerator p.1 p.2)),
        J = Complex.I • complexify M) ∧
    (∀ a b c d : Phase n, algebraCommutator (generatorMatrix a b) (generatorMatrix c d) =
      Complex.I • ((sigma n a c : ℂ) • generatorMatrix b d +
        (sigma n b c : ℂ) • generatorMatrix a d + (sigma n a d : ℂ) • generatorMatrix c b +
        (sigma n b d : ℂ) • generatorMatrix c a)) ∧
    (∀ J : Matrix (Phase n) (Phase n) ℂ,
      (∀ c d, star (J c d) = -J c d) →
      (complexify (sigma n) * J).IsSymm → (J * complexify (sigma n)).IsSymm →
      ∀ t : ℝ, let E := NormedSpace.exp ((-Complex.I * (t : ℂ)) • J)
        (∀ a b, (E a b).im = 0) ∧ PreservesCanonicalForm (fun a b => (E a b).re)) := by
  refine ⟨fun a b => ⟨?_, good_of_mem (R_mem a b)⟩, linIndep, finrank_span, fun J => ⟨?_, ?_⟩,
    part5, ?_⟩
  · unfold generatorMatrix; congr 2; ext c d; simp only [realGenerator]; ring
  · rintro ⟨h1, h2, -⟩; exact char_fwd J h1 h2
  · rintro ⟨M, hM, rfl⟩; exact good_of_mem (span_le hM)
  · intro J h1 h2 h3 t
    obtain ⟨M, hM, rfl⟩ := char_fwd J h1 h2
    have hM' := span_le hM
    have heq : (-Complex.I * (t : ℂ)) • (Complex.I • complexify M) = complexify (t • M) := by
      rw [smul_smul, cx_smul]; congr 1
      rw [mul_comm (-Complex.I), mul_assoc, neg_mul, Complex.I_mul_I]; ring
    simp only
    rw [heq, exp_cx]
    refine ⟨fun a b => by simp [complexify], ?_⟩
    have : (fun a b => (complexify (NormedSpace.exp (t • M)) a b).re) = NormedSpace.exp (t • M) := by
      ext a b; simp [complexify]
    rw [this]
    apply exp_symp
    rw [Matrix.smul_mul]; exact hM'.2.smul t
