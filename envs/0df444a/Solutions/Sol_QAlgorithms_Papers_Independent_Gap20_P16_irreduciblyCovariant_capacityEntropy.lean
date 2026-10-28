-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P16.irreduciblyCovariant_capacityEntropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T22:50:34.455631+00:00
-- url     : https://prove2.me/submissions/b7c81e48-bf73-4701-8592-2d3664aa8725

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P16

-- ===== WYA =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [AddCommGroup H]

lemma cv_add_left (b b' : CharacterGroup H) (a : H) :
    characterValue (b + b') a = characterValue b a * characterValue b' a := by
  simp [characterValue]

lemma cv_add_right (b : CharacterGroup H) (a a' : H) :
    characterValue b (a + a') = characterValue b a * characterValue b a' := by
  simp [characterValue, AddChar.map_add_eq_mul]

lemma cv_zero_left (a : H) : characterValue (0 : CharacterGroup H) a = 1 := by
  simp [characterValue]

lemma cv_zero_right (b : CharacterGroup H) : characterValue b (0 : H) = 1 := by
  simp [characterValue]

lemma cv_norm (b : CharacterGroup H) (a : H) : ‖characterValue b a‖ = 1 :=
  Circle.norm_coe _

lemma cv_conj_mul (b : CharacterGroup H) (a : H) :
    conj (characterValue b a) * characterValue b a = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, cv_norm]; simp

lemma cv_mul_conj (b : CharacterGroup H) (a : H) :
    characterValue b a * conj (characterValue b a) = 1 := by
  rw [mul_comm, cv_conj_mul]

lemma cv_neg_left (b : CharacterGroup H) (a : H) :
    characterValue (-b) a = conj (characterValue b a) := by
  have h := cv_add_left (-b) b a
  rw [neg_add_cancel, cv_zero_left] at h
  have h2 := cv_conj_mul b a
  calc characterValue (-b) a = characterValue (-b) a * (characterValue b a * conj (characterValue b a)) := by
        rw [cv_mul_conj, mul_one]
    _ = conj (characterValue b a) := by rw [← mul_assoc, ← h, one_mul]

lemma cv_neg_right (b : CharacterGroup H) (a : H) :
    characterValue b (-a) = conj (characterValue b a) := by
  have h := cv_add_right b (-a) a
  rw [neg_add_cancel, cv_zero_right] at h
  calc characterValue b (-a) = characterValue b (-a) * (characterValue b a * conj (characterValue b a)) := by
        rw [cv_mul_conj, mul_one]
    _ = conj (characterValue b a) := by rw [← mul_assoc, ← h, one_mul]

lemma cv_sub_right (b : CharacterGroup H) (a a' : H) :
    characterValue b (a - a') = characterValue b a * conj (characterValue b a') := by
  rw [sub_eq_add_neg, cv_add_right, cv_neg_right]

lemma cv_sub_left (b b' : CharacterGroup H) (a : H) :
    characterValue (b - b') a = characterValue b a * conj (characterValue b' a) := by
  rw [sub_eq_add_neg, cv_add_left, cv_neg_left]

/-- Nontrivial characters exist. -/
lemma exists_cv_ne_one [Finite H] {a : H} (ha : a ≠ 0) :
    ∃ b : CharacterGroup H, characterValue b a ≠ 1 := by
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := a)).2 ha
  refine ⟨Additive.ofMul (AddChar.circleEquivComplex.symm ψ), ?_⟩
  have : ((AddChar.circleEquivComplex.symm ψ) a : ℂ) = ψ a := rfl
  simpa [characterValue, this] using hψ

lemma exists_cv_ne_one' {b : CharacterGroup H} (hb : b ≠ 0) :
    ∃ a : H, characterValue b a ≠ 1 := by
  by_contra h
  push Not at h
  apply hb
  change Additive.ofMul (Additive.toMul b) = Additive.ofMul 1
  congr 1
  ext a
  have := h a
  simp only [characterValue] at this
  simpa using this

variable {d : ℕ}

/-- shorthand for a Weyl operator as a matrix -/
abbrev Wm (W : FiniteAbelianWeylSystem H d) (z : H × CharacterGroup H) : Matrix (Fin d) (Fin d) ℂ :=
  (finiteAbelianWeylOperator W z : Mat d)

lemma Wm_def (W : FiniteAbelianWeylSystem H d) (z : H × CharacterGroup H) :
    Wm W z = (W.U z.1 : Mat d) * (W.V z.2 : Mat d) := by
  simp [Wm, finiteAbelianWeylOperator]

lemma Wm_star_mul (W : FiniteAbelianWeylSystem H d) (z) : (Wm W z)ᴴ * Wm W z = 1 :=
  Matrix.mem_unitaryGroup_iff'.1 (finiteAbelianWeylOperator W z).2

lemma Wm_mul_star (W : FiniteAbelianWeylSystem H d) (z) : Wm W z * (Wm W z)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.1 (finiteAbelianWeylOperator W z).2

lemma U_add' (W : FiniteAbelianWeylSystem H d) (a a' : H) :
    (W.U (a + a') : Mat d) = (W.U a : Mat d) * (W.U a' : Mat d) := by
  rw [W.U_add]; rfl

lemma V_add' (W : FiniteAbelianWeylSystem H d) (b b' : CharacterGroup H) :
    (W.V (b + b') : Mat d) = (W.V b : Mat d) * (W.V b' : Mat d) := by
  rw [W.V_add]; rfl

/-- product law -/
lemma Wm_mul (W : FiniteAbelianWeylSystem H d) (z w : H × CharacterGroup H) :
    Wm W z * Wm W w = characterValue z.2 w.1 • Wm W (z + w) := by
  rw [Wm_def, Wm_def, Wm_def, Prod.fst_add, Prod.snd_add, U_add', V_add']
  calc (W.U z.1 : Mat d) * (W.V z.2 : Mat d) * ((W.U w.1 : Mat d) * (W.V w.2 : Mat d))
      = (W.U z.1 : Mat d) * ((W.V z.2 : Mat d) * (W.U w.1 : Mat d)) * (W.V w.2 : Mat d) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [W.commutation]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

lemma Wm_zero (W : FiniteAbelianWeylSystem H d) : Wm W 0 = 1 := by
  simp [Wm_def, W.U_zero, W.V_zero]

/-- commutation phase: `W zᴴ W w W z = pair z w • W w` -/
def pair (z w : H × CharacterGroup H) : ℂ :=
  characterValue w.2 z.1 * conj (characterValue z.2 w.1)

lemma pair_norm (z w : H × CharacterGroup H) : ‖pair z w‖ = 1 := by
  simp [pair, cv_norm]

lemma pair_conj_mul (z w : H × CharacterGroup H) : conj (pair z w) * pair z w = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, pair_norm]; simp

lemma pair_mul_conj (z w : H × CharacterGroup H) : pair z w * conj (pair z w) = 1 := by
  rw [mul_comm, pair_conj_mul]

lemma pair_add_left (z z' w : H × CharacterGroup H) :
    pair (z + z') w = pair z w * pair z' w := by
  simp only [pair, Prod.fst_add, Prod.snd_add, cv_add_left, cv_add_right, map_mul]; ring

lemma pair_add_right (z w w' : H × CharacterGroup H) :
    pair z (w + w') = pair z w * pair z w' := by
  simp only [pair, Prod.fst_add, Prod.snd_add, cv_add_left, cv_add_right, map_mul]; ring

lemma pair_zero_left (w : H × CharacterGroup H) : pair 0 w = 1 := by
  simp [pair, cv_zero_left, cv_zero_right]

lemma pair_zero_right (z : H × CharacterGroup H) : pair z 0 = 1 := by
  simp [pair, cv_zero_left, cv_zero_right]

lemma pair_sub_right (z w w' : H × CharacterGroup H) :
    pair z (w - w') = pair z w * conj (pair z w') := by
  have h := pair_add_right z (w - w') w'
  rw [sub_add_cancel] at h
  calc pair z (w - w') = pair z (w - w') * (pair z w' * conj (pair z w')) := by
        rw [pair_mul_conj, mul_one]
    _ = pair z w * conj (pair z w') := by rw [← mul_assoc, ← h]

lemma Wm_conj (W : FiniteAbelianWeylSystem H d) (z w : H × CharacterGroup H) :
    (Wm W z)ᴴ * Wm W w * Wm W z = pair z w • Wm W w := by
  have h1 := Wm_mul W w z
  have h2 := Wm_mul W z w
  rw [add_comm] at h1
  -- W w W z = cv w.2 z.1 • W(z+w), W z W w = cv z.2 w.1 • W (z+w)
  have h3 : Wm W w * Wm W z = (characterValue w.2 z.1 * conj (characterValue z.2 w.1)) •
      (Wm W z * Wm W w) := by
    rw [h1, h2, smul_smul, mul_assoc, cv_conj_mul, mul_one]
  rw [Matrix.mul_assoc, h3, Matrix.mul_smul, ← Matrix.mul_assoc, Wm_star_mul, Matrix.one_mul]
  rfl

lemma Wm_conj' (W : FiniteAbelianWeylSystem H d) (z w : H × CharacterGroup H) :
    Wm W z * Wm W w * (Wm W z)ᴴ = conj (pair z w) • Wm W w := by
  have h := Wm_conj W z w
  have : Wm W w = pair z w • (Wm W z * Wm W w * (Wm W z)ᴴ) := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← h]
    simp only [Matrix.mul_assoc, Wm_mul_star, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Wm_mul_star, Matrix.one_mul]
  conv_rhs => rw [this, smul_smul, pair_conj_mul, one_smul]

/-- `W zᴴ W s = pair z s • W s W zᴴ` -/
lemma Wm_star_comm (W : FiniteAbelianWeylSystem H d) (z s : H × CharacterGroup H) :
    (Wm W z)ᴴ * Wm W s = pair z s • (Wm W s * (Wm W z)ᴴ) := by
  have h := Wm_conj W z s
  calc (Wm W z)ᴴ * Wm W s = (Wm W z)ᴴ * Wm W s * Wm W z * (Wm W z)ᴴ := by
        rw [Matrix.mul_assoc _ (Wm W z), Wm_mul_star, Matrix.mul_one]
    _ = _ := by rw [h, Matrix.smul_mul]

variable [Fintype H] [Fintype (CharacterGroup H)]

lemma exists_pair_ne_one {w : H × CharacterGroup H} (hw : w ≠ 0) :
    ∃ z, pair z w ≠ 1 := by
  by_cases h2 : w.2 = 0
  · have h1 : w.1 ≠ 0 := by
      intro h1; apply hw; ext <;> simp [h1, h2]
    obtain ⟨b, hb⟩ := exists_cv_ne_one h1
    refine ⟨(0, b), ?_⟩
    simp only [pair, cv_zero_right, one_mul]
    intro h; apply hb
    have := congrArg conj h
    simpa using this
  · obtain ⟨a, ha⟩ := exists_cv_ne_one' h2
    refine ⟨(a, 0), ?_⟩
    simpa [pair, cv_zero_left] using ha

lemma sum_pair_eq_zero {w : H × CharacterGroup H} (hw : w ≠ 0) :
    ∑ z, pair z w = 0 := by
  obtain ⟨z0, hz0⟩ := exists_pair_ne_one hw
  have h : ∑ z, pair z w = pair z0 w * ∑ z, pair z w := by
    rw [Finset.mul_sum]
    simp_rw [← pair_add_left]
    exact (Fintype.sum_equiv (Equiv.addLeft z0) _ _ (fun _ => rfl)).symm
  have : (1 - pair z0 w) * ∑ z, pair z w = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd (sub_eq_zero.1 h1).symm hz0
  · exact h1

/-- orthogonality of the commutation phases -/
lemma sum_pair_orth (w w' : H × CharacterGroup H) :
    ∑ z, pair z w * conj (pair z w') =
      if w = w' then (Fintype.card (H × CharacterGroup H) : ℂ) else 0 := by
  simp_rw [← pair_sub_right]
  split_ifs with h
  · subst h; simp [pair_zero_right]
  · exact sum_pair_eq_zero (sub_ne_zero.2 h)

lemma trace_Wm (W : FiniteAbelianWeylSystem H d) {w : H × CharacterGroup H} (hw : w ≠ 0) :
    (Wm W w).trace = 0 := by
  obtain ⟨z, hz⟩ := exists_pair_ne_one hw
  have h := congrArg Matrix.trace (Wm_conj W z w)
  rw [Matrix.trace_mul_cycle, Wm_mul_star, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul] at h
  have : (1 - pair z w) * (Wm W w).trace = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd (sub_eq_zero.1 h1).symm hz
  · exact h1

lemma Wm_star_mul_eq (W : FiniteAbelianWeylSystem H d) (z w : H × CharacterGroup H) :
    (Wm W z)ᴴ * Wm W w = conj (characterValue z.2 (w - z).1) • Wm W (w - z) := by
  have h := Wm_mul W z (w - z)
  rw [add_sub_cancel] at h
  have h2 := congrArg (fun M => (Wm W z)ᴴ * M) h
  simp only [← Matrix.mul_assoc, Wm_star_mul, Matrix.one_mul, Matrix.mul_smul] at h2
  rw [h2, smul_smul, cv_conj_mul, one_smul]

lemma trace_star_mul (W : FiniteAbelianWeylSystem H d) (z w : H × CharacterGroup H) :
    ((Wm W z)ᴴ * Wm W w).trace = if z = w then (d : ℂ) else 0 := by
  split_ifs with h
  · subst h; rw [Wm_star_mul]; simp
  · rw [Wm_star_mul_eq, Matrix.trace_smul, trace_Wm W (sub_ne_zero.2 (Ne.symm h)), smul_zero]

end X4WY

-- ===== WYB =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Schur's lemma for the matrix-level irreducibility predicate. -/
lemma schur {G : Type*} {d : ℕ} (hd : 0 < d) (ρ : G → Mat d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible ρ)
    (T : Mat d) (hT : ∀ g, ρ g * T = T * ρ g) : ∃ c : ℂ, T = c • 1 := by
  haveI : Nontrivial (Fin d → ℂ) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' T)
  set S := Module.End.eigenspace (Matrix.toLin' T) μ
  have hinv : ∀ g v, v ∈ S → (ρ g).mulVec v ∈ S := by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    simp only [Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hT, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  rcases hirr.2 S hinv with h | h
  · exact absurd h hμ
  · refine ⟨μ, ?_⟩
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have hv : v ∈ S := by rw [h]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]
    simp [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]

variable {H : Type*} [AddCommGroup H] [Fintype H] [Fintype (CharacterGroup H)] {d : ℕ}

local notation "GG" => H × CharacterGroup H

/-- twirl -/
def tw (W : FiniteAbelianWeylSystem H d) (X : Mat d) : Mat d :=
  ∑ s : GG, Wm W s * X * (Wm W s)ᴴ

lemma Wm_mul_ad (W : FiniteAbelianWeylSystem H d) (z s : GG) (X : Mat d) :
    Wm W z * (Wm W s * X * (Wm W s)ᴴ) * (Wm W z)ᴴ = Wm W (z + s) * X * (Wm W (z + s))ᴴ := by
  have h := Wm_mul W z s
  calc Wm W z * (Wm W s * X * (Wm W s)ᴴ) * (Wm W z)ᴴ
      = (Wm W z * Wm W s) * X * (Wm W z * Wm W s)ᴴ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [h, Matrix.conjTranspose_smul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [show star (characterValue z.2 s.1) * characterValue z.2 s.1 = 1 from cv_conj_mul _ _,
          one_smul]

lemma tw_comm (W : FiniteAbelianWeylSystem H d) (X : Mat d) (z : GG) :
    Wm W z * tw W X = tw W X * Wm W z := by
  have h : Wm W z * tw W X * (Wm W z)ᴴ = tw W X := by
    simp only [tw, Matrix.mul_sum, Matrix.sum_mul]
    simp_rw [Wm_mul_ad]
    exact Fintype.sum_equiv (Equiv.addLeft z) _ _ (fun _ => rfl)
  calc Wm W z * tw W X = Wm W z * tw W X * (Wm W z)ᴴ * Wm W z := by
        rw [Matrix.mul_assoc _ _ (Wm W z), Wm_star_mul, Matrix.mul_one]
    _ = _ := by rw [h]

lemma trace_tw (W : FiniteAbelianWeylSystem H d) (X : Mat d) :
    (tw W X).trace = (Fintype.card GG : ℂ) * X.trace := by
  simp only [tw, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (Wm W _) X, Wm_star_mul, Matrix.one_mul]
  simp

lemma tw_eq (hd : 0 < d) (W : FiniteAbelianWeylSystem H d)
    (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun z => Wm W z))
    (X : Mat d) : tw W X = ((Fintype.card GG : ℂ) * X.trace / d) • 1 := by
  obtain ⟨c, hc⟩ := schur hd _ hirr (tw W X) (fun z => tw_comm W X z)
  have ht := trace_tw W X
  rw [hc, Matrix.trace_smul, Matrix.trace_one] at ht
  simp only [Fintype.card_fin, smul_eq_mul] at ht
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hc]; congr 1
  field_simp
  rw [← ht]

end X4WY

-- ===== WYG =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ}

lemma cont_xlog : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
  have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (x * Real.log x) / Real.log 2 := by
    funext x; rw [Real.logb]; ring
  rw [this]; exact Real.continuous_mul_log.div_const _

lemma cfc_trace {Y : Matrix (Fin d) (Fin d) ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eig {Y : Matrix (Fin d) (Fin d) ℂ} (hY : Y.IsHermitian) :
    vnEntropy Y = -∑ i, hY.eigenvalues i * Real.logb 2 (hY.eigenvalues i) := by
  unfold vnEntropy
  rw [cfc_trace hY]
  simp [Complex.re_sum]

lemma dens_eig {ρ : Matrix (Fin d) (Fin d) ℂ} (h : IsDensityMatrix ρ) :
    (∀ i, 0 ≤ h.1.1.eigenvalues i) ∧ ∑ i, h.1.1.eigenvalues i = 1 := by
  refine ⟨fun i => h.1.eigenvalues_nonneg i, ?_⟩
  have e2 := h.1.1.trace_eq_sum_eigenvalues.symm.trans h.2
  have h2 := congrArg Complex.re e2
  simp only [Complex.one_re, Complex.re_sum] at h2
  simpa using h2

lemma dens_spec {ρ : Matrix (Fin d) (Fin d) ℂ} (h : IsDensityMatrix ρ) :
    IsSelfAdjoint ρ ∧ spectrum ℝ ρ ⊆ Set.Icc 0 1 := by
  refine ⟨h.1.1, ?_⟩
  rw [h.1.1.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  obtain ⟨h0, h1⟩ := dens_eig h
  refine ⟨h0 i, ?_⟩
  rw [← h1]
  exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

lemma vn_le_log (hd : 0 < d) {ρ : Matrix (Fin d) (Fin d) ℂ} (h : IsDensityMatrix ρ) :
    vnEntropy ρ ≤ Real.logb 2 d := by
  rw [vn_eig h.1.1]
  obtain ⟨h0, h1⟩ := dens_eig h
  have hD : (0:ℝ) < d := by exact_mod_cast hd
  have key : ∀ μ : ℝ, 0 ≤ μ → -(μ * Real.log μ) - μ * Real.log d ≤ 1 / d - μ := by
    intro μ hμ
    rcases hμ.eq_or_lt with h | h
    · subst h; simp
    · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (d * μ) by positivity)
      rw [one_div, Real.log_inv, Real.log_mul hD.ne' h.ne'] at h1
      have h2 : μ * ((d * μ)⁻¹ - 1) = 1 / d - μ := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left h1 h.le]
  set μ := h.1.1.eigenvalues
  have k2 : ∑ i, (-(μ i * Real.log (μ i)) - μ i * Real.log d) ≤
      ∑ _i : Fin d, (1 / (d : ℝ)) - ∑ i, μ i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => key _ (h0 i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, h1, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_fin, mul_one_div_cancel hD.ne'] at k2
  simp only [Real.logb, ← Finset.sum_neg_distrib]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : ∑ i, -(μ i * (Real.log (μ i) / Real.log 2)) =
      (∑ i, -(μ i * Real.log (μ i))) / Real.log 2 := by
    rw [Finset.sum_div]; congr 1; ext i; ring
  rw [this, div_le_div_iff_of_pos_right hl]
  linarith

lemma vn_scalar (hd : 0 < d) : vnEntropy (((1 / d : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) =
    Real.logb 2 d := by
  unfold vnEntropy
  have e : (((1 / d : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) =
      algebraMap ℝ (Matrix (Fin d) (Fin d) ℂ) (1 / d) := by
    rw [Algebra.algebraMap_eq_smul_one]; rfl
  rw [e, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin]
  have hD : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  rw [one_div, Real.logb_inv]
  field_simp

lemma vn_unitary {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.IsHermitian)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    vnEntropy (U * ρ * Uᴴ) = vnEntropy ρ := by
  unfold vnEntropy
  set u : unitary (Matrix (Fin d) (Fin d) ℂ) := ⟨U, hU⟩
  have hφ : Continuous (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) u) := by
    have : (⇑(Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) u)) = fun X => U * X * star U := by
      funext X; rfl
    rw [this]; fun_prop
  have hρ' : IsSelfAdjoint ρ := hρ
  have hρ2 : IsSelfAdjoint (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) u ρ) := by
    rw [Unitary.conjStarAlgAut_apply]
    exact (IsSelfAdjoint.conjugate hρ' _)
  have := StarAlgHomClass.map_cfc (S := ℂ) (R := ℝ) (p := IsSelfAdjoint) (q := IsSelfAdjoint)
    (Unitary.conjStarAlgAut ℂ (Matrix (Fin d) (Fin d) ℂ) u)
    (fun x : ℝ => x * Real.logb 2 x) ρ cont_xlog.continuousOn hφ hρ' hρ2
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply] at this
  rw [show Uᴴ = star U from rfl]
  simp only [u] at this
  rw [← this]
  rw [Matrix.trace_mul_cycle, show star U * U = 1 from Matrix.mem_unitaryGroup_iff'.1 hU,
    Matrix.one_mul]

open scoped Matrix.Norms.L2Operator in
lemma vn_contOn :
    ContinuousOn (fun ρ : Matrix (Fin d) (Fin d) ℂ => vnEntropy ρ)
      {a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Icc 0 1} := by
  have h := continuousOn_cfc (Matrix (Fin d) (Fin d) ℂ) (isCompact_Icc (a := (0:ℝ)) (b := 1))
    (fun x : ℝ => x * Real.logb 2 x) cont_xlog.continuousOn
  have h2 : Continuous (fun M : Matrix (Fin d) (Fin d) ℂ => -(M.trace.re)) := by fun_prop
  exact h2.comp_continuousOn h

/-- entries of a density matrix are bounded by one -/
lemma dens_entry {ρ : Matrix (Fin d) (Fin d) ℂ} (h : IsDensityMatrix ρ) (i j : Fin d) :
    ‖ρ i j‖ ≤ 1 := by
  have hs := h.1.1.spectral_theorem
  obtain ⟨h0, h1⟩ := dens_eig h
  set U := (h.1.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ := h.1.1.eigenvectorUnitary.2
  have e : ρ i j = ∑ k, U i k * (h.1.1.eigenvalues k : ℂ) * star (U j k) := by
    conv_lhs => rw [hs]
    rw [Unitary.conjStarAlgAut_apply]
    simp [Matrix.mul_apply, Matrix.diagonal, U, Matrix.star_apply]
  rw [e]
  calc ‖∑ k, U i k * (h.1.1.eigenvalues k : ℂ) * star (U j k)‖
      ≤ ∑ k, ‖U i k * (h.1.1.eigenvalues k : ℂ) * star (U j k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, h.1.1.eigenvalues k := by
        apply Finset.sum_le_sum; intro k _
        rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (h0 k)]
        have a1 := entry_norm_bound_of_unitary hU i k
        have a2 := entry_norm_bound_of_unitary hU j k
        have := h0 k
        calc ‖U i k‖ * h.1.1.eigenvalues k * ‖U j k‖ ≤ 1 * h.1.1.eigenvalues k * 1 := by
              gcongr
          _ = _ := by ring
    _ = 1 := h1

lemma dens_closed : IsClosed {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensityMatrix ρ} := by
  have e : {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensityMatrix ρ} =
      {ρ | ρᴴ = ρ} ∩ (⋂ x : Fin d → ℂ, {ρ | 0 ≤ star x ⬝ᵥ (ρ *ᵥ x)}) ∩ {ρ | ρ.trace = 1} := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, IsDensityMatrix,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [e]
  refine (IsClosed.inter (IsClosed.inter ?_ ?_) ?_)
  · exact isClosed_eq (by fun_prop) continuous_id
  · refine isClosed_iInter fun x => ?_
    exact isClosed_le continuous_const (by fun_prop)
  · exact isClosed_eq (by fun_prop) continuous_const

lemma dens_compact : IsCompact {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensityMatrix ρ} := by
  have hbox : IsCompact (Set.univ.pi fun _ : Fin d => Set.univ.pi fun _ : Fin d =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (s := Set.univ.pi fun _ : Fin d => Set.univ.pi fun _ : Fin d =>
      Metric.closedBall (0 : ℂ) 1) hbox dens_closed ?_
  intro ρ hρ
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => dens_entry hρ i j

end X4WY

-- ===== WYH =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- convex hull of a compact set in a finite-dimensional space is compact (Carathéodory) -/
lemma hull_compact {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  rcases s.eq_empty_or_nonempty with h | ⟨z0, hz0⟩
  · subst h; simp
  set N := Module.finrank ℝ E + 1
  set S : Set ((Fin N → ℝ) × (Fin N → E)) := stdSimplex ℝ (Fin N) ×ˢ Set.univ.pi fun _ => s
  have hS : IsCompact S := IsCompact.prod (isCompact_stdSimplex ℝ (Fin N)) (isCompact_univ_pi fun _ => hs)
  set F : (Fin N → ℝ) × (Fin N → E) → E := fun p => ∑ i, p.1 i • p.2 i
  have hF : Continuous F := by fun_prop
  have e : convexHull ℝ s = F '' S := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ι, _, z, w, hz, _hai, hw0, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      have hcard : Fintype.card ι ≤ N := by
        have := _hai.card_le_finrank_succ
        have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
        simp only [N]; omega
      obtain ⟨f⟩ : Nonempty (ι ↪ Fin N) := Function.Embedding.nonempty_of_card_le (by simpa using hcard)
      refine ⟨(Function.extend f w 0, Function.extend f z (fun _ => z0)), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro k
        dsimp only
        by_cases hk : ∃ i, f i = k
        · obtain ⟨i, rfl⟩ := hk; rw [f.injective.extend_apply]; exact (hw0 i).le
        · rw [Function.extend_apply' _ _ _ hk]; simp
      · have h1 : ∑ k, Function.extend f w 0 k = ∑ k ∈ Finset.univ.map f, Function.extend f w 0 k := by
          symm; apply Finset.sum_subset (Finset.subset_univ _)
          intro k _ hk
          have : ¬ ∃ i, f i = k := by
            rintro ⟨i, rfl⟩; exact hk (Finset.mem_map_of_mem f (Finset.mem_univ i))
          rw [Function.extend_apply' _ _ _ this]; simp
        rw [h1, Finset.sum_map]
        simp_rw [f.injective.extend_apply]; exact hw1
      · intro k _
        dsimp only
        by_cases hk : ∃ i, f i = k
        · obtain ⟨i, rfl⟩ := hk; rw [f.injective.extend_apply]; exact hz ⟨i, rfl⟩
        · rw [Function.extend_apply' _ _ _ hk]; exact hz0
      · simp only [F]
        have h1 : ∑ k, Function.extend f w 0 k • Function.extend f z (fun _ => z0) k =
            ∑ k ∈ Finset.univ.map f,
              Function.extend f w 0 k • Function.extend f z (fun _ => z0) k := by
          symm; apply Finset.sum_subset (Finset.subset_univ _)
          intro k _ hk
          have : ¬ ∃ i, f i = k := by
            rintro ⟨i, rfl⟩; exact hk (Finset.mem_map_of_mem f (Finset.mem_univ i))
          rw [Function.extend_apply' _ _ _ this]; simp
        rw [h1, Finset.sum_map]
        simp_rw [f.injective.extend_apply]; exact hx
    · rintro x ⟨⟨w, z⟩, ⟨⟨hw0, hw1⟩, hz⟩, rfl⟩
      exact (convex_convexHull ℝ s).sum_mem (fun i _ => hw0 i) hw1
        (fun i _ => subset_convexHull ℝ s (hz i (Set.mem_univ i)))
  rw [e]; exact hS.image hF

variable {d : ℕ}

/-- squared Frobenius norm -/
def fro (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Xᴴ * X).trace.re

lemma fro_eq (X : Matrix (Fin d) (Fin d) ℂ) : fro X = ∑ i, ∑ k, Complex.normSq (X k i) := by
  simp only [fro, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  rw [Complex.normSq_apply]
  simp [Complex.mul_re]

lemma fro_nonneg (X : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ fro X := by
  rw [fro_eq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _

lemma fro_eq_zero {X : Matrix (Fin d) (Fin d) ℂ} (h : fro X = 0) : X = 0 := by
  rw [fro_eq] at h
  ext k i
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
    (fun k _ => Complex.normSq_nonneg (X k i)))).1 h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Complex.normSq_nonneg (X k i))).1 h1 k
    (Finset.mem_univ _)
  simpa using h2

lemma fro_cont : Continuous (fun X : Matrix (Fin d) (Fin d) ℂ => fro X) := by
  unfold fro; fun_prop

lemma fro_conj (X U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    fro (U * X * Uᴴ) = fro X := by
  unfold fro
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have : (U * X * Uᴴ)ᴴ * (U * X * Uᴴ) = U * (Xᴴ * X) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, h1, Matrix.one_mul]
  rw [this, Matrix.trace_mul_cycle, h1, Matrix.one_mul]

lemma fro_mid (X Y : Matrix (Fin d) (Fin d) ℂ) :
    fro ((1 / 2 : ℝ) • X + (1 / 2 : ℝ) • Y) = (fro X + fro Y) / 2 - fro (X - Y) / 4 := by
  unfold fro
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Complex.add_re,
    Complex.sub_re, star_trivial, Complex.real_smul, Complex.smul_re, smul_eq_mul]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  ring

/-- a compact convex set invariant under a family of unitary conjugations has a common fixed point -/
lemma fixed_point {G : Type*} (V : G → Matrix (Fin d) (Fin d) ℂ)
    (hV : ∀ g, V g ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {K : Set (Matrix (Fin d) (Fin d) ℂ)} (hK : IsCompact K) (hKc : Convex ℝ K) (hne : K.Nonempty)
    (hinv : ∀ g, ∀ X ∈ K, V g * X * (V g)ᴴ ∈ K) :
    ∃ X0 ∈ K, ∀ g, V g * X0 * (V g)ᴴ = X0 := by
  obtain ⟨X0, hX0, hmin⟩ := hK.exists_isMinOn hne fro_cont.continuousOn
  refine ⟨X0, hX0, fun g => ?_⟩
  set Y := V g * X0 * (V g)ᴴ
  have hY : Y ∈ K := hinv g X0 hX0
  have hfY : fro Y = fro X0 := fro_conj X0 (V g) (hV g)
  have hmid : (1 / 2 : ℝ) • X0 + (1 / 2 : ℝ) • Y ∈ K :=
    hKc hX0 hY (by norm_num) (by norm_num) (by norm_num)
  have h1 := hmin hmid
  simp only [Set.mem_setOf_eq] at h1
  rw [fro_mid, hfY] at h1
  have h2 : fro (X0 - Y) = 0 := le_antisymm (by linarith) (fro_nonneg _)
  exact (sub_eq_zero.1 (fro_eq_zero h2)).symm

end X4WY

-- ===== WYI =====

noncomputable section

namespace X4WY

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {d : ℕ}

section Kraus

variable {m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ)

lemma kr_add (X Y : Matrix (Fin d) (Fin d) ℂ) :
    krausApply E (X + Y) = krausApply E X + krausApply E Y := by
  simp only [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

lemma kr_smul (c : ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    krausApply E (c • X) = c • krausApply E X := by
  simp only [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

lemma kr_rsmul (c : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) :
    krausApply E (c • X) = c • krausApply E X := by
  rw [← Complex.coe_smul, kr_smul, Complex.coe_smul]

lemma kr_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (X : ι → Matrix (Fin d) (Fin d) ℂ) :
    krausApply E (∑ i ∈ s, c i • X i) = ∑ i ∈ s, c i • krausApply E (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using kr_smul E 0 0
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, kr_add, kr_rsmul, ih]

lemma kr_trace (hK : ∑ j, (E j)ᴴ * E j = 1) (X : Matrix (Fin d) (Fin d) ℂ) :
    (krausApply E X).trace = X.trace := by
  simp only [krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) X, ← Matrix.trace_sum, ← Finset.sum_mul, hK,
    Matrix.one_mul]

lemma kr_dens (hK : ∑ j, (E j)ᴴ * E j = 1) {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsDensityMatrix X) :
    IsDensityMatrix (krausApply E X) :=
  ⟨Matrix.posSemidef_sum _ (fun j _ => hX.1.mul_mul_conjTranspose_same (E j)),
    (kr_trace E hK X).trans hX.2⟩

lemma kr_cont : Continuous (krausApply E) := by
  unfold krausApply; fun_prop

end Kraus

lemma dens_conj {X : Matrix (Fin d) (Fin d) ℂ} (hX : IsDensityMatrix X) (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) : IsDensityMatrix (U * X * Uᴴ) :=
  ⟨hX.1.mul_mul_conjTranspose_same U, by
    rw [Matrix.trace_mul_cycle, show Uᴴ * U = 1 from Matrix.mem_unitaryGroup_iff'.1 hU,
      Matrix.one_mul]; exact hX.2⟩

lemma scalar_dens (hd : 0 < d) : IsDensityMatrix (((1 / d : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ)) := by
  refine ⟨Matrix.PosSemidef.one.smul ?_, ?_⟩
  · have : (0 : ℝ) ≤ 1 / d := by positivity
    exact_mod_cast this
  · rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast; field_simp

lemma proj_conj {G : Type*} [Group G] [TopologicalSpace G] (V : ProjectiveRepresentation G d)
    (h g : G) (X : Matrix (Fin d) (Fin d) ℂ) :
    (V.unitary h : Matrix (Fin d) (Fin d) ℂ) * ((V.unitary g : Matrix (Fin d) (Fin d) ℂ) * X *
      (V.unitary g : Matrix (Fin d) (Fin d) ℂ)ᴴ) * (V.unitary h : Matrix (Fin d) (Fin d) ℂ)ᴴ =
    (V.unitary (h * g) : Matrix (Fin d) (Fin d) ℂ) * X * (V.unitary (h * g) : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  obtain ⟨c, hc, he⟩ := V.multiply h g
  rw [he]
  have hcc : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  have hcc' : star c * c = 1 := by rw [mul_comm]; exact hcc
  rw [Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcc, hcc', one_smul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem cap_main (hd : 0 < d) {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (V1 V2 : ProjectiveRepresentation G d)
    (hirr1 : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun g => (V1.unitary g : Mat d)))
    (hirr2 : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun g => (V2.unitary g : Mat d)))
    (hcov : CovariantBetween Phi V1.unitary V2.unitary) :
    Phi 1 = 1 ∧ CapacityEntropyIdentity Phi := by
  obtain ⟨m, E, hK, hPhiE⟩ := hPhi
  have hPhi' : Phi = krausApply E := funext hPhiE
  subst hPhi'
  have hK' : ∑ j, (E j)ᴴ * E j = 1 := hK
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  -- unitality
  have hunit : krausApply E 1 = 1 := by
    obtain ⟨c, hc⟩ := schur hd (fun g => (V2.unitary g : Mat d)) hirr2 (krausApply E 1) (by
      intro g
      have h := hcov g 1
      simp only [unitaryAction, Matrix.mul_one] at h
      rw [show (V1.unitary g : Mat d) * (V1.unitary g : Mat d)ᴴ = 1 from
        Matrix.mem_unitaryGroup_iff.1 (V1.unitary g).2] at h
      conv_rhs => rw [h]
      simp only [Matrix.mul_assoc]
      rw [show (V2.unitary g : Mat d)ᴴ * (V2.unitary g : Mat d) = 1 from
        Matrix.mem_unitaryGroup_iff'.1 (V2.unitary g).2, Matrix.mul_one])
    have ht := kr_trace E hK' 1
    rw [hc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at ht
    have : c = 1 := by
      have := mul_right_cancel₀ hd' (ht.trans (one_mul _).symm)
      exact this
    rw [hc, this, one_smul]
  refine ⟨hunit, ?_⟩
  -- minimizer
  set D := {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensityMatrix ρ}
  have hcont : ContinuousOn (fun ρ => vnEntropy (krausApply E ρ)) D := by
    refine vn_contOn.comp (kr_cont E).continuousOn ?_
    intro ρ hρ
    exact dens_spec (kr_dens E hK' hρ)
  obtain ⟨ρs, hρs, hmin⟩ := dens_compact.exists_isMinOn ⟨_, scalar_dens hd⟩ hcont
  have hlow : ∀ σ, IsDensityMatrix σ → vnEntropy (krausApply E ρs) ≤ vnEntropy (krausApply E σ) :=
    fun σ hσ => hmin hσ
  have hup : ∀ σ, IsDensityMatrix σ → vnEntropy (krausApply E σ) ≤ Real.logb 2 d :=
    fun σ hσ => vn_le_log hd (kr_dens E hK' hσ)
  set Smin := vnEntropy (krausApply E ρs)
  -- the orbit and its convex hull
  set O := Set.range (fun g => unitaryAction (V1.unitary g) ρs)
  have hO : IsCompact O := isCompact_range (V1.continuous_conjugation ρs)
  have hKc : IsCompact (convexHull ℝ O) := hull_compact hO
  have hinv : ∀ h, ∀ X ∈ convexHull ℝ O,
      (V1.unitary h : Mat d) * X * (V1.unitary h : Mat d)ᴴ ∈ convexHull ℝ O := by
    intro h X hX
    have hlin : IsLinearMap ℝ (fun X : Matrix (Fin d) (Fin d) ℂ =>
        (V1.unitary h : Mat d) * X * (V1.unitary h : Mat d)ᴴ) :=
      ⟨fun X Y => by simp only [Matrix.mul_add, Matrix.add_mul],
       fun c X => by simp only [Matrix.mul_smul, Matrix.smul_mul]⟩
    have h1 : (fun X : Matrix (Fin d) (Fin d) ℂ =>
        (V1.unitary h : Mat d) * X * (V1.unitary h : Mat d)ᴴ) '' O ⊆ O := by
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨h * g, (proj_conj V1 h g ρs).symm⟩
    have h2 := Set.mem_image_of_mem (fun X : Matrix (Fin d) (Fin d) ℂ =>
        (V1.unitary h : Mat d) * X * (V1.unitary h : Mat d)ᴴ) hX
    rw [hlin.image_convexHull] at h2
    exact convexHull_mono h1 h2
  have hne : (convexHull ℝ O).Nonempty :=
    ⟨_, subset_convexHull ℝ O ⟨1, rfl⟩⟩
  obtain ⟨X0, hX0, hfix⟩ := fixed_point (fun g => (V1.unitary g : Mat d)) (fun g => (V1.unitary g).2)
    hKc (convex_convexHull ℝ O) hne hinv
  have htr : ∀ X ∈ convexHull ℝ O, X.trace = 1 := by
    have hconv : Convex ℝ {X : Matrix (Fin d) (Fin d) ℂ | X.trace = 1} := by
      intro X hX Y hY a b _ _ hab
      simp only [Set.mem_ofPred_eq] at hX hY ⊢
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX, hY]
      simp only [Complex.real_smul, mul_one]
      exact_mod_cast hab
    refine fun X hX => convexHull_min ?_ hconv hX
    rintro _ ⟨g, rfl⟩
    exact (dens_conj hρs _ (V1.unitary g).2).2
  have hX0eq : X0 = ((1 / d : ℝ) : ℂ) • 1 := by
    obtain ⟨c, hc⟩ := schur hd (fun g => (V1.unitary g : Mat d)) hirr1 X0 (by
      intro g
      conv_rhs => rw [← hfix g]
      simp only [Matrix.mul_assoc]
      rw [show (V1.unitary g : Mat d)ᴴ * (V1.unitary g : Mat d) = 1 from
        Matrix.mem_unitaryGroup_iff'.1 (V1.unitary g).2, Matrix.mul_one])
    have ht := htr X0 hX0
    rw [hc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at ht
    rw [hc]; congr 1
    push_cast
    field_simp
    exact ht
  -- the attaining ensemble
  rw [hX0eq] at hX0
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.1 hX0
  have hzS : ∀ i, vnEntropy (krausApply E (z i)) = Smin := by
    intro i
    obtain ⟨g, hg⟩ := hz i
    rw [← hg]
    have := hcov g ρs
    rw [this]
    exact vn_unitary (kr_dens E hK' hρs).1.1 _ (V2.unitary g).2
  have hzD : ∀ i, IsDensityMatrix (z i) := by
    intro i
    obtain ⟨g, hg⟩ := hz i
    rw [← hg]; exact dens_conj hρs _ (V1.unitary g).2
  have havg : vnEntropy (krausApply E (((1 / d : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ))) =
      Real.logb 2 d := by
    rw [kr_smul, hunit]; exact vn_scalar hd
  set e := Fintype.equivFin ι
  let ens : QAlgorithms.Papers.Independent.Information100.P08.Ensemble (Fin d) :=
    { size := Fintype.card ι
      prob := fun k => w (e.symm k)
      state := fun k => z (e.symm k)
      nonneg := fun k => hw0 _
      total := by rw [← hw1]; exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
      density := fun k => hzD _ }
  have hens : QAlgorithms.Papers.Independent.Information100.P08.outputHolevo (krausApply E) ens =
      Real.logb 2 d - Smin := by
    unfold QAlgorithms.Papers.Independent.Information100.P08.outputHolevo
      QAlgorithms.Papers.Independent.Information100.P08.ensembleAverage
    have h1 : ∑ x, ens.prob x • ens.state x = ((1 / d : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
      rw [← hsum]; exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    rw [h1, havg]
    congr 1
    have h2 : ∑ x, ens.prob x * vnEntropy (krausApply E (ens.state x)) = ∑ x, ens.prob x * Smin := by
      apply Finset.sum_congr rfl; intro x _; simp only [ens]; rw [hzS]
    rw [h2, ← Finset.sum_mul, ens.total, one_mul]
  have hgreat : IsGreatest {v | ∃ (m : ℕ) (q : Fin m → ℝ) (rho : Fin m → Matrix (Fin d) (Fin d) ℂ),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j = 1) ∧ (∀ j, IsDensityMatrix (rho j)) ∧
      v = vnEntropy (krausApply E (∑ j, (q j : ℂ) • rho j)) - ∑ j, q j * vnEntropy (krausApply E (rho j))}
      (Real.logb 2 d - Smin) := by
    refine ⟨⟨ens.size, ens.prob, ens.state, ens.nonneg, ens.total, ens.density, ?_⟩, ?_⟩
    · rw [← hens]
      unfold QAlgorithms.Papers.Independent.Information100.P08.outputHolevo
        QAlgorithms.Papers.Independent.Information100.P08.ensembleAverage
      simp only [Complex.coe_smul]
    · rintro v ⟨m', q, ρ, h0, h1, h2, rfl⟩
      have hav : IsDensityMatrix (∑ j, (q j : ℂ) • ρ j) := by
        refine ⟨Matrix.posSemidef_sum _ (fun j _ => (h2 j).1.smul (by exact_mod_cast h0 j)), ?_⟩
        rw [Matrix.trace_sum]
        simp only [Matrix.trace_smul, (h2 _).2, smul_eq_mul, mul_one]
        exact_mod_cast h1
      have ha := hup _ hav
      have hb : ∑ j, q j * Smin ≤ ∑ j, q j * vnEntropy (krausApply E (ρ j)) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hlow _ (h2 j)) (h0 j)
      rw [← Finset.sum_mul, h1, one_mul] at hb
      linarith
  have hcap : QAlgorithms.Papers.Independent.Dependency50.P45.holevoCapacity (krausApply E) =
      Real.logb 2 d - Smin := hgreat.csSup_eq
  exact ⟨ρs, hρs, hlow, hcap, ens, hens.trans hcap.symm⟩

end X4WY

-- ===== WYSol4 =====

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P16
open QAlgorithms.Papers.Independent.Information100.P26 (Mat Unitary)

section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution
    {d : ℕ} (hd : 0 < d) {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (V : ProjectiveRepresentation G d) (hirr : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (fun g => (V.unitary g : Mat d)))
    (hcov : CovariantBetween Phi V.unitary V.unitary) :
    Phi 1 = 1 ∧ CapacityEntropyIdentity Phi :=
  X4WY.cap_main hd Phi hPhi V V hirr hirr hcov

end
