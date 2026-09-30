-- Prove2me | solution 1 for UnderstandingML.rip_l1_recovery
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T14:19:30.525727+00:00
-- url     : https://prove2.me/submissions/9aa3c0a7-f26f-4ff1-a288-0536ef1ac5f3

import Definitions.Def_UnderstandingML_DimReduction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.Chebyshev

open MeasureTheory ProbabilityTheory

namespace UnderstandingML.CandesAux

variable {n d : ℕ}

/-! ### Euclidean norm of plain vectors -/

/-- The Euclidean norm `‖v‖₂ = √(∑ vᵢ²)`. -/
noncomputable def nrm (v : Fin d → ℝ) : ℝ := Real.sqrt (sqNorm v)

lemma sqNorm_nonneg (v : Fin d → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma nrm_nonneg (v : Fin d → ℝ) : 0 ≤ nrm v := Real.sqrt_nonneg _

lemma nrm_sq (v : Fin d → ℝ) : nrm v ^ 2 = sqNorm v := Real.sq_sqrt (sqNorm_nonneg v)

lemma nrm_eq_norm (v : Fin d → ℝ) : nrm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq, nrm, sqNorm]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Real.norm_eq_abs, sq_abs]

lemma nrm_add_le (u v : Fin d → ℝ) : nrm (u + v) ≤ nrm u + nrm v := by
  simp only [nrm_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

lemma nrm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin d → ℝ) :
    nrm (∑ j ∈ s, f j) ≤ ∑ j ∈ s, nrm (f j) := by
  simp only [nrm_eq_norm, WithLp.toLp_sum]
  exact norm_sum_le _ _

lemma sqNorm_eq_dot (v : Fin d → ℝ) : sqNorm v = v ⬝ᵥ v := by
  simp [sqNorm, dotProduct, sq]

lemma sqNorm_restrictTo (S : Finset (Fin d)) (v : Fin d → ℝ) :
    sqNorm (restrictTo S v) = ∑ i ∈ S, v i ^ 2 := by
  simp only [sqNorm, restrictTo]
  have : ∀ i, (if i ∈ S then v i else 0) ^ 2 = if i ∈ S then v i ^ 2 else 0 := by
    intro i; split_ifs <;> simp
  simp_rw [this]
  rw [Finset.sum_ite_mem]
  simp

/-! ### RIP consequences -/

lemma l0Norm_le_of_support {v : Fin d → ℝ} (S : Finset (Fin d)) (hv : ∀ i, i ∉ S → v i = 0) :
    l0Norm v ≤ S.card := by
  classical
  unfold l0Norm
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_contra hS
  exact hi (hv i hS)

lemma sqNorm_pos {v : Fin d → ℝ} (hv : v ≠ 0) : 0 < sqNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  unfold sqNorm
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun j => v j ^ 2)
    (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

lemma rip_lower {ε : ℝ} {s : ℕ} {W : Matrix (Fin n) (Fin d) ℝ} (hW : IsRIP ε s W)
    (v : Fin d → ℝ) (hv : l0Norm v ≤ s) : (1 - ε) * sqNorm v ≤ sqNorm (W.mulVec v) := by
  by_cases h0 : v = 0
  · subst h0
    simp [sqNorm]
  · have hpos := sqNorm_pos h0
    have h := hW v h0 hv
    have h2 := (abs_le.mp h).1
    have : 1 - ε ≤ sqNorm (W.mulVec v) / sqNorm v := by linarith
    rwa [le_div_iff₀ hpos] at this

lemma rip_upper {ε : ℝ} {s : ℕ} {W : Matrix (Fin n) (Fin d) ℝ} (hW : IsRIP ε s W)
    (v : Fin d → ℝ) (hv : l0Norm v ≤ s) : sqNorm (W.mulVec v) ≤ (1 + ε) * sqNorm v := by
  by_cases h0 : v = 0
  · subst h0
    simp [sqNorm]
  · have hpos := sqNorm_pos h0
    have h := hW v h0 hv
    have h2 := (abs_le.mp h).2
    have : sqNorm (W.mulVec v) / sqNorm v ≤ 1 + ε := by linarith
    rwa [div_le_iff₀ hpos] at this

lemma l0Norm_add_le (u v : Fin d → ℝ) : l0Norm (u + v) ≤ l0Norm u + l0Norm v := by
  classical
  unfold l0Norm
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply,
    Finset.mem_union] at hi ⊢
  by_contra h
  push Not at h
  exact hi (by rw [h.1, h.2, add_zero])

lemma l0Norm_smul_le (c : ℝ) (u : Fin d → ℝ) : l0Norm (c • u) ≤ l0Norm u := by
  classical
  unfold l0Norm
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.smul_apply,
    smul_eq_mul] at hi ⊢
  intro h
  exact hi (by rw [h, mul_zero])

/-- **Lemma 23.10.** For vectors with disjoint supports of size at most `s` and an
`(ε, 2s)`-RIP matrix, `|⟨Wu, Wv⟩| ≤ ε ‖u‖ ‖v‖`. -/
lemma rip_inner_le {ε : ℝ} {s : ℕ} {W : Matrix (Fin n) (Fin d) ℝ} (hW : IsRIP ε (2 * s) W)
    (u v : Fin d → ℝ) (hu : l0Norm u ≤ s) (hv : l0Norm v ≤ s) (huv : ∀ i, u i = 0 ∨ v i = 0) :
    |(W.mulVec u) ⬝ᵥ (W.mulVec v)| ≤ ε * nrm u * nrm v := by
  by_cases hu0 : u = 0
  · subst hu0; simp [nrm, sqNorm]
  by_cases hv0 : v = 0
  · subst hv0; simp [nrm, sqNorm]
  have hnu : 0 < nrm u := Real.sqrt_pos.mpr (sqNorm_pos hu0)
  have hnv : 0 < nrm v := Real.sqrt_pos.mpr (sqNorm_pos hv0)
  set a := (nrm u)⁻¹ • u with ha
  set b := (nrm v)⁻¹ • v with hb
  have hsa : a ⬝ᵥ a = 1 := by
    rw [ha, smul_dotProduct, dotProduct_smul, ← sqNorm_eq_dot, ← nrm_sq, smul_eq_mul,
      smul_eq_mul]
    field_simp
  have hsb : b ⬝ᵥ b = 1 := by
    rw [hb, smul_dotProduct, dotProduct_smul, ← sqNorm_eq_dot, ← nrm_sq, smul_eq_mul,
      smul_eq_mul]
    field_simp
  have hab : a ⬝ᵥ b = 0 := by
    have : u ⬝ᵥ v = 0 := by
      unfold dotProduct
      exact Finset.sum_eq_zero (fun i _ => by rcases huv i with h | h <;> simp [h])
    rw [ha, hb, smul_dotProduct, dotProduct_smul, this]; simp
  have hl0a : l0Norm a ≤ s := le_trans (l0Norm_smul_le _ _) hu
  have hl0b : l0Norm b ≤ s := le_trans (l0Norm_smul_le _ _) hv
  have hl0p : l0Norm (a + b) ≤ 2 * s := by
    have := l0Norm_add_le a b; omega
  have hl0m : l0Norm (a + (-1 : ℝ) • b) ≤ 2 * s := by
    have := l0Norm_add_le a ((-1 : ℝ) • b)
    have := l0Norm_smul_le (-1 : ℝ) b
    omega
  have hba : b ⬝ᵥ a = 0 := by rw [dotProduct_comm]; exact hab
  have hsp : sqNorm (a + b) = 2 := by
    simp only [sqNorm_eq_dot, add_dotProduct, dotProduct_add, hsa, hsb, hab, hba]; norm_num
  have hsm : sqNorm (a + (-1 : ℝ) • b) = 2 := by
    simp only [sqNorm_eq_dot, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      hsa, hsb, hab, hba, smul_eq_mul]; norm_num
  have h1 := rip_upper hW _ hl0p
  have h2 := rip_lower hW _ hl0p
  have h3 := rip_upper hW _ hl0m
  have h4 := rip_lower hW _ hl0m
  rw [hsp] at h1 h2
  rw [hsm] at h3 h4
  have hpol : sqNorm (W.mulVec (a + b)) - sqNorm (W.mulVec (a + (-1 : ℝ) • b)) =
      4 * ((W.mulVec a) ⬝ᵥ (W.mulVec b)) := by
    simp only [sqNorm_eq_dot, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, dotProduct_comm (W.mulVec b) (W.mulVec a)]
    simp; ring
  have hWab : |(W.mulVec a) ⬝ᵥ (W.mulVec b)| ≤ ε := by
    rw [abs_le]; constructor <;> linarith
  have huv' : (W.mulVec u) ⬝ᵥ (W.mulVec v) = nrm u * nrm v * ((W.mulVec a) ⬝ᵥ (W.mulVec b)) := by
    rw [ha, hb, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    field_simp
  rw [huv', abs_mul, abs_of_pos (mul_pos hnu hnv)]
  calc nrm u * nrm v * |(W.mulVec a) ⬝ᵥ (W.mulVec b)| ≤ nrm u * nrm v * ε :=
        mul_le_mul_of_nonneg_left hWab (by positivity)
    _ = ε * nrm u * nrm v := by ring


lemma sqNorm_add_disjoint (u v : Fin d → ℝ) (huv : ∀ i, u i = 0 ∨ v i = 0) :
    sqNorm (u + v) = sqNorm u + sqNorm v := by
  unfold sqNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases huv i with h | h <;> simp [h]

lemma sum_blocks (f : ℕ → ℝ) (s M : ℕ) :
    ∑ j ∈ Finset.range M, ∑ k ∈ Finset.Ico (j * s) ((j + 1) * s), f k =
      ∑ k ∈ Finset.range (M * s), f k := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_add_sum_Ico _ (by nlinarith)]

lemma div_eq_iff_mem_Ico {s : ℕ} (hs : 0 < s) (k j : ℕ) :
    k / s = j ↔ k ∈ Finset.Ico (j * s) ((j + 1) * s) := by
  rw [Finset.mem_Ico]
  constructor
  · rintro rfl
    refine ⟨Nat.div_mul_le_self k s, ?_⟩
    have h1 := Nat.div_add_mod k s
    have h2 := Nat.mod_lt k hs
    nlinarith
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hs).mpr h2)
    · exact (Nat.le_div_iff_mul_le hs).mpr h1

/-- The final real-number bookkeeping of Candès' argument. -/
lemma final_arith (ε e A Sb L a0 H S : ℝ) (hS : 0 < S) (hε0 : 0 ≤ ε)
    (hε : ε < 1 / (1 + Real.sqrt 2)) (hA : 0 ≤ A) (hSb : 0 ≤ Sb)
    (F1 : H ≤ A + Sb) (F2 : Sb ≤ L / S) (F3 : L ≤ S * a0 + 2 * e) (F4 : a0 ≤ A)
    (F5 : (1 - ε) * A ^ 2 ≤ Real.sqrt 2 * ε * A * Sb) :
    H ≤ 2 * (1 + Real.sqrt 2 * ε / (1 - ε)) / (1 - Real.sqrt 2 * ε / (1 - ε)) * (1 / S) * e := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have h2' : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hε1 : ε * (1 + Real.sqrt 2) < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hε; linarith
  have h1ε : 0 < 1 - ε := by nlinarith
  set ρ := Real.sqrt 2 * ε / (1 - ε) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one h1ε]; nlinarith
  -- `A ≤ ρ Sb`
  have hAρ : A ≤ ρ * Sb := by
    rcases hA.eq_or_lt with hA0 | hApos
    · rw [← hA0]; positivity
    · have : (1 - ε) * A ≤ Real.sqrt 2 * ε * Sb := by
        have := F5
        nlinarith
      rw [hρ, div_mul_eq_mul_div, le_div_iff₀ h1ε]; linarith
  -- `Sb ≤ A + 2e/S`
  have hSb2 : Sb ≤ A + 2 * e / S := by
    have : L / S ≤ a0 + 2 * e / S := by
      rw [div_le_iff₀ hS]; rw [add_mul, div_mul_cancel₀ _ hS.ne']; linarith
    linarith
  have hA2 : A * (1 - ρ) ≤ ρ * (2 * e / S) := by nlinarith
  have hA3 : A ≤ ρ * (2 * e / S) / (1 - ρ) := by
    rw [le_div_iff₀ (by linarith)]; exact hA2
  have hfin : H ≤ 2 * A + 2 * e / S := by linarith
  have hgoal : 2 * (1 + ρ) / (1 - ρ) * (1 / S) * e =
      2 * (ρ * (2 * e / S) / (1 - ρ)) + 2 * e / S := by
    have h1ρ : 1 - ρ ≠ 0 := by linarith
    field_simp
    ring
  rw [hgoal]; linarith

/-! ### The block decomposition -/

/-- A pure inequality for a nonnegative antitone sequence: the `ℓ₂` norm of block `j + 1` is at
most `s^{-1/2}` times the `ℓ₁` norm of block `j`. -/
lemma block_bound (G : ℕ → ℝ) (hG : Antitone G) (h0 : ∀ k, 0 ≤ G k) {s : ℕ} (hs : 0 < s)
    (j : ℕ) :
    Real.sqrt (∑ k ∈ Finset.Ico ((j + 1) * s) ((j + 2) * s), G k ^ 2) ≤
      (∑ k ∈ Finset.Ico (j * s) ((j + 1) * s), G k) / Real.sqrt s := by
  set P := ∑ k ∈ Finset.Ico (j * s) ((j + 1) * s), G k with hP
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  -- every entry of the later block is at most the average of the earlier block
  have hle : ∀ k ∈ Finset.Ico ((j + 1) * s) ((j + 2) * s), G k * s ≤ P := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hcard : ((Finset.Ico (j * s) ((j + 1) * s)).card : ℝ) = s := by
      rw [Nat.card_Ico]; push_cast [Nat.cast_sub (by nlinarith : j * s ≤ (j + 1) * s)]; ring
    calc G k * s = ∑ _k' ∈ Finset.Ico (j * s) ((j + 1) * s), G k := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
      _ ≤ P := Finset.sum_le_sum (fun k' hk' => by
          rw [Finset.mem_Ico] at hk'
          exact hG (by omega))
  have hP0 : 0 ≤ P := Finset.sum_nonneg (fun k _ => h0 k)
  have hsq : ∑ k ∈ Finset.Ico ((j + 1) * s) ((j + 2) * s), G k ^ 2 ≤ P ^ 2 / s := by
    have hcard : ((Finset.Ico ((j + 1) * s) ((j + 2) * s)).card : ℝ) = s := by
      rw [Nat.card_Ico]
      push_cast [Nat.cast_sub (by nlinarith : (j + 1) * s ≤ (j + 2) * s)]; ring
    calc ∑ k ∈ Finset.Ico ((j + 1) * s) ((j + 2) * s), G k ^ 2
        ≤ ∑ _k ∈ Finset.Ico ((j + 1) * s) ((j + 2) * s), (P / s) ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          have := hle k hk
          have hGk : G k ≤ P / s := by rw [le_div_iff₀ hsR]; exact this
          exact pow_le_pow_left₀ (h0 k) hGk 2
      _ = P ^ 2 / s := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]; field_simp
  calc Real.sqrt (∑ k ∈ Finset.Ico ((j + 1) * s) ((j + 2) * s), G k ^ 2)
      ≤ Real.sqrt (P ^ 2 / s) := Real.sqrt_le_sqrt hsq
    _ = P / Real.sqrt s := by
      rw [Real.sqrt_div' _ hsR.le, Real.sqrt_sq hP0]

/-- A sorted enumeration of a finset of indices by decreasing `|h|`. -/
lemma exists_sorted_enum (C : Finset (Fin d)) (h : Fin d → ℝ) :
    ∃ σ : Fin C.card → Fin d, Function.Injective σ ∧ (∀ k, σ k ∈ C) ∧
      Antitone (fun k => |h (σ k)|) := by
  let e : Fin C.card ≃ C := C.equivFin.symm
  let f : Fin C.card → ℝ := fun k => -|h (e k)|
  let π := Tuple.sort f
  refine ⟨fun k => (e (π k)).val, ?_, fun k => (e (π k)).property, ?_⟩
  · intro k₁ k₂ hk
    have := Subtype.val_injective hk
    exact π.injective (e.injective this)
  · intro k₁ k₂ hk
    have := Tuple.monotone_sort f hk
    simp only [Function.comp_apply, f] at this
    simp only
    linarith

lemma exists_sorted_enum' (C : Finset (Fin d)) (h : Fin d → ℝ) :
    ∃ (N : ℕ) (σ : Fin N → Fin d), Function.Injective σ ∧ (∀ k, σ k ∈ C) ∧
      (∀ i ∈ C, ∃ k, σ k = i) ∧ Antitone (fun k => |h (σ k)|) := by
  obtain ⟨σ, hσinj, hσC, hσanti⟩ := exists_sorted_enum C h
  refine ⟨C.card, σ, hσinj, hσC, ?_, hσanti⟩
  have himg : Finset.univ.image σ = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi
      obtain ⟨k, rfl⟩ := hi
      exact hσC k
    · rw [Finset.card_image_of_injective _ hσinj]; simp
  intro i hi
  rw [← himg] at hi
  simpa using hi

end UnderstandingML.CandesAux

open UnderstandingML UnderstandingML.CandesAux in
theorem solution {n d s : ℕ} (hs : 0 < s) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < 1 / (1 + Real.sqrt 2)) (W : Matrix (Fin n) (Fin d) ℝ) (hW : IsRIP ε (2 * s) W)
    (x xs xstar : Fin d → ℝ) (hxs : l0Norm xs ≤ s)
    (_hxs_min : ∀ v, l0Norm v ≤ s → l1Norm (x - xs) ≤ l1Norm (x - v))
    (hy : W.mulVec xstar = W.mulVec x)
    (hmin : ∀ v, W.mulVec v = W.mulVec x → l1Norm xstar ≤ l1Norm v) :
    Real.sqrt (sqNorm (xstar - x)) ≤
      2 * (1 + Real.sqrt 2 * ε / (1 - ε)) / (1 - Real.sqrt 2 * ε / (1 - ε)) *
        (s : ℝ) ^ (-(1 : ℝ) / 2) * l1Norm (x - xs) := by
  classical
  set h : Fin d → ℝ := xstar - x with hh
  set e := l1Norm (x - xs) with he
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hSpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hsR
  set T0 : Finset (Fin d) := Finset.univ.filter (fun i => xs i ≠ 0) with hT0
  set C : Finset (Fin d) := Finset.univ.filter (fun i => ¬ xs i ≠ 0) with hC
  have hT0card : T0.card ≤ s := by
    have := hxs; unfold l0Norm at this; convert this
  have hmemC : ∀ i, i ∈ C ↔ xs i = 0 := by intro i; simp [hC]
  have hmemT0 : ∀ i, i ∈ T0 ↔ xs i ≠ 0 := by intro i; simp [hT0]
  have hsplit : ∀ F : Fin d → ℝ, ∑ i, F i = ∑ i ∈ T0, F i + ∑ i ∈ C, F i := fun F =>
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  obtain ⟨N, σ, hσinj, hσC, hσsurj, hσanti⟩ := exists_sorted_enum' C h
  let σe : Fin N ↪ Fin d := ⟨σ, hσinj⟩
  let B : ℕ → Finset (Fin d) := fun j =>
    (Finset.univ.filter (fun k : Fin N => k.val / s = j)).map σe
  let G : ℕ → ℝ := fun k => if hk : k < N then |h (σ ⟨k, hk⟩)| else 0
  have hG0 : ∀ k, 0 ≤ G k := by
    intro k; simp only [G]; split_ifs <;> simp
  have hGanti : Antitone G := by
    intro k₁ k₂ hk
    by_cases h1 : k₁ < N <;> by_cases h2 : k₂ < N
    · simp only [G, h1, h2, dif_pos]
      exact hσanti (show (⟨k₁, h1⟩ : Fin N) ≤ ⟨k₂, h2⟩ from hk)
    · simp only [G, h1, h2, dif_pos, dif_neg, not_false_eq_true]
      exact abs_nonneg _
    · omega
    · simp only [G, h1, h2, dif_neg, not_false_eq_true, le_refl]
  have hmemB : ∀ (k : Fin N) j, σ k ∈ B j ↔ k.val / s = j := by
    intro k j
    simp only [B, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k', hk', hk'k⟩
      have : k' = k := hσinj hk'k
      rw [← this]; exact hk'
    · intro hk; exact ⟨k, hk, rfl⟩
  have hBC : ∀ j, B j ⊆ C := by
    intro j i hi
    simp only [B, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨k, _, rfl⟩ := hi
    exact hσC k
  have hBcard : ∀ j, (B j).card ≤ s := by
    intro j
    simp only [B, Finset.card_map]
    calc (Finset.univ.filter (fun k : Fin N => k.val / s = j)).card
        = ((Finset.univ.filter (fun k : Fin N => k.val / s = j)).map Fin.valEmbedding).card :=
          (Finset.card_map _).symm
      _ ≤ (Finset.Ico (j * s) ((j + 1) * s)).card := by
          apply Finset.card_le_card
          intro k hk
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.valEmbedding_apply] at hk
          obtain ⟨k', hk', rfl⟩ := hk
          exact (div_eq_iff_mem_Ico hs _ _).mp hk'
      _ = s := by rw [Nat.card_Ico]; rw [add_mul, one_mul]; omega
  have hBdisj : ∀ j j', j ≠ j' → ∀ i, i ∈ B j → i ∉ B j' := by
    intro j j' hjj' i hi hi'
    obtain ⟨k, rfl⟩ := hσsurj i (hBC j hi)
    rw [hmemB] at hi hi'
    exact hjj' (hi.symm.trans hi')
  have hBsum : ∀ φ : ℝ → ℝ, φ 0 = 0 → ∀ j,
      ∑ i ∈ B j, φ |h i| = ∑ k ∈ Finset.Ico (j * s) ((j + 1) * s), φ (G k) := by
    intro φ hφ j
    simp only [B, Finset.sum_map]
    have h1 : ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val / s = j), φ |h (σe k)| =
        ∑ k ∈ (Finset.univ.filter (fun k : Fin N => k.val / s = j)).map Fin.valEmbedding,
          φ (G k) := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [G, k.isLt, σe]
    rw [h1]
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply] at hk
      obtain ⟨k', hk', rfl⟩ := hk
      exact (div_eq_iff_mem_Ico hs _ _).mp hk'
    · intro k hk hk'
      have hkN : ¬ k < N := by
        intro hkN
        apply hk'
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply]
        exact ⟨⟨k, hkN⟩, (div_eq_iff_mem_Ico hs _ _).mpr hk, rfl⟩
      simp [G, hkN, hφ]
  have hCsum : ∀ M, ∑ k ∈ Finset.range M, G k ≤ ∑ i ∈ C, |h i| := by
    intro M
    have hC' : ∑ i ∈ C, |h i| = ∑ k ∈ Finset.range N, G k := by
      have himg : C = Finset.univ.map σe := by
        ext i
        simp only [Finset.mem_map, Finset.mem_univ, true_and]
        constructor
        · intro hi; exact hσsurj i hi
        · rintro ⟨k, rfl⟩; exact hσC k
      rw [himg, Finset.sum_map, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp [G, k.isLt, σe]
    rw [hC']
    calc ∑ k ∈ Finset.range M, G k
        = ∑ k ∈ (Finset.range M).filter (· < N), G k := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          split_ifs with hk
          · rfl
          · simp [G, hk]
      _ ≤ ∑ k ∈ Finset.range N, G k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
            exact hk.2
          · intro k _ _; exact hG0 k
  -- the decomposition `h = h_{T0} + ∑_j h_{B_j}`
  have hdecomp : h = restrictTo T0 h + ∑ j ∈ Finset.range (N + 1), restrictTo (B j) h := by
    funext i
    simp only [Pi.add_apply, Finset.sum_apply, restrictTo]
    by_cases hi : i ∈ T0
    · rw [if_pos hi]
      have : ∀ j, i ∉ B j := by
        intro j hj
        have := (hmemC i).mp (hBC j hj)
        exact ((hmemT0 i).mp hi) this
      simp [this]
    · rw [if_neg hi]
      have hiC : i ∈ C := by rw [hmemC]; by_contra h'; exact hi ((hmemT0 i).mpr h')
      obtain ⟨k, rfl⟩ := hσsurj i hiC
      simp only [hmemB, zero_add]
      rw [Finset.sum_ite_eq]
      rw [if_pos]
      simp only [Finset.mem_range]
      have := k.isLt
      have : k.val / s ≤ k.val := Nat.div_le_self _ _
      omega
  set u0 := restrictTo T0 h with hu0
  set u1 := restrictTo (B 0) h with hu1
  set r : ℕ → Fin d → ℝ := fun j => restrictTo (B (j + 1)) h with hr
  have hdecomp' : h = (u0 + u1) + ∑ j ∈ Finset.range N, r j := by
    conv_lhs => rw [hdecomp]
    rw [Finset.sum_range_succ']
    abel
  have hWh : W.mulVec h = 0 := by
    rw [hh, Matrix.mulVec_sub, hy, sub_self]
  set A := nrm (u0 + u1) with hA
  set a0 := nrm u0 with ha0
  set a1 := nrm u1 with ha1
  set b : ℕ → ℝ := fun j => nrm (r j) with hb
  set Sb := ∑ j ∈ Finset.range N, b j with hSb
  set L := ∑ i ∈ C, |h i| with hL
  have hrestr_sq : ∀ S : Finset (Fin d), nrm (restrictTo S h) = Real.sqrt (∑ i ∈ S, h i ^ 2) := by
    intro S; rw [nrm, sqNorm_restrictTo]
  -- disjointness facts
  have hdisj01 : ∀ i, u0 i = 0 ∨ u1 i = 0 := by
    intro i
    by_cases hi : i ∈ B 0
    · left
      have := (hmemC i).mp (hBC 0 hi)
      simp only [hu0, restrictTo, hmemT0, this, ne_eq, not_true_eq_false, if_false]
    · right; simp [hu1, restrictTo, hi]
  have hdisj0r : ∀ j i, u0 i = 0 ∨ r j i = 0 := by
    intro j i
    by_cases hi : i ∈ B (j + 1)
    · left
      have := (hmemC i).mp (hBC (j + 1) hi)
      simp only [hu0, restrictTo, hmemT0, this, ne_eq, not_true_eq_false, if_false]
    · right; simp [hr, restrictTo, hi]
  have hdisj1r : ∀ j i, u1 i = 0 ∨ r j i = 0 := by
    intro j i
    by_cases hi : i ∈ B 0
    · right
      have := hBdisj 0 (j + 1) (by omega) i hi
      simp [hr, restrictTo, this]
    · left; simp [hu1, restrictTo, hi]
  -- F1
  have F1 : nrm h ≤ A + Sb := by
    calc nrm h = nrm ((u0 + u1) + ∑ j ∈ Finset.range N, r j) := by rw [← hdecomp']
      _ ≤ nrm (u0 + u1) + nrm (∑ j ∈ Finset.range N, r j) := nrm_add_le _ _
      _ ≤ A + Sb := by
          have := nrm_sum_le (Finset.range N) r
          linarith
  -- F2
  have F2 : Sb ≤ L / Real.sqrt s := by
    have hbj : ∀ j, b j ≤ (∑ k ∈ Finset.Ico (j * s) ((j + 1) * s), G k) / Real.sqrt s := by
      intro j
      have e1 : b j = Real.sqrt (∑ k ∈ Finset.Ico ((j + 1) * s) ((j + 1 + 1) * s), G k ^ 2) := by
        simp only [hb, hr]
        rw [hrestr_sq]
        congr 1
        have := hBsum (fun t => t ^ 2) (by norm_num) (j + 1)
        simp only [sq_abs] at this
        exact this
      rw [e1]
      exact block_bound G hGanti hG0 hs j
    calc Sb ≤ ∑ j ∈ Finset.range N,
          (∑ k ∈ Finset.Ico (j * s) ((j + 1) * s), G k) / Real.sqrt s :=
          Finset.sum_le_sum (fun j _ => hbj j)
      _ = (∑ k ∈ Finset.range (N * s), G k) / Real.sqrt s := by
          rw [← Finset.sum_div, sum_blocks]
      _ ≤ L / Real.sqrt s := div_le_div_of_nonneg_right (hCsum _) hSpos.le
  -- F3: the cone inequality
  have F3 : L ≤ Real.sqrt s * a0 + 2 * e := by
    have hl1 := hmin x rfl
    have hxstar : xstar = x + h := by rw [hh]; abel
    have hxC : ∑ i ∈ C, |x i| ≤ e := by
      rw [he, l1Norm, hsplit]
      have : ∑ i ∈ C, |(x - xs) i| = ∑ i ∈ C, |x i| := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        simp [(hmemC i).mp hi]
      rw [this]
      have : 0 ≤ ∑ i ∈ T0, |(x - xs) i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
      linarith
    have hT0le : ∑ i ∈ T0, |x i| - ∑ i ∈ T0, |h i| ≤ ∑ i ∈ T0, |xstar i| := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [hxstar]
      have := abs_add_le (x i + h i) (-h i)
      simp only [add_neg_cancel_right, abs_neg] at this
      simp only [Pi.add_apply]
      linarith
    have hCle : L - ∑ i ∈ C, |x i| ≤ ∑ i ∈ C, |xstar i| := by
      rw [hL, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [hxstar]
      have := abs_add_le (x i + h i) (-x i)
      simp only [add_neg_cancel_comm, abs_neg] at this
      simp only [Pi.add_apply]
      linarith
    have hl1' : ∑ i ∈ T0, |xstar i| + ∑ i ∈ C, |xstar i| ≤ ∑ i ∈ T0, |x i| + ∑ i ∈ C, |x i| := by
      rw [← hsplit, ← hsplit]; exact hl1
    have hcs : ∑ i ∈ T0, |h i| ≤ Real.sqrt s * a0 := by
      rw [ha0, hu0, hrestr_sq, ← Real.sqrt_mul hsR.le]
      apply Real.le_sqrt_of_sq_le
      calc (∑ i ∈ T0, |h i|) ^ 2 ≤ T0.card * ∑ i ∈ T0, |h i| ^ 2 := sq_sum_le_card_mul_sum_sq
        _ ≤ s * ∑ i ∈ T0, h i ^ 2 := by
          simp only [sq_abs]
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast hT0card)
          exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    linarith
  -- F4
  have hA2 : A ^ 2 = a0 ^ 2 + a1 ^ 2 := by
    rw [hA, ha0, ha1, nrm_sq, nrm_sq, nrm_sq, sqNorm_add_disjoint _ _ hdisj01]
  have F4 : a0 ≤ A := by
    have h0 : 0 ≤ a0 := nrm_nonneg _
    have h1 : 0 ≤ A := nrm_nonneg _
    nlinarith [sq_nonneg a1]
  -- F5
  have F5 : (1 - ε) * A ^ 2 ≤ Real.sqrt 2 * ε * A * Sb := by
    have hl0 : l0Norm (u0 + u1) ≤ 2 * s := by
      calc l0Norm (u0 + u1) ≤ (T0 ∪ B 0).card := by
            apply l0Norm_le_of_support
            intro i hi
            simp only [Finset.mem_union, not_or] at hi
            simp [hu0, hu1, restrictTo, hi.1, hi.2]
        _ ≤ T0.card + (B 0).card := Finset.card_union_le _ _
        _ ≤ 2 * s := by have := hBcard 0; omega
    have hlow := rip_lower hW (u0 + u1) hl0
    rw [← nrm_sq] at hlow
    have hl0u0 : l0Norm u0 ≤ s := le_trans (l0Norm_le_of_support T0 (by
      intro i hi; simp [hu0, restrictTo, hi])) hT0card
    have hl0u1 : l0Norm u1 ≤ s := le_trans (l0Norm_le_of_support (B 0) (by
      intro i hi; simp [hu1, restrictTo, hi])) (hBcard 0)
    have hl0r : ∀ j, l0Norm (r j) ≤ s := fun j => le_trans (l0Norm_le_of_support (B (j + 1)) (by
      intro i hi; simp [hr, restrictTo, hi])) (hBcard (j + 1))
    have hWsum : W.mulVec (u0 + u1) = -∑ j ∈ Finset.range N, W.mulVec (r j) := by
      have := hWh
      rw [hdecomp', Matrix.mulVec_add, Matrix.mulVec_sum] at this
      exact eq_neg_of_add_eq_zero_left this
    have hsq : sqNorm (W.mulVec (u0 + u1)) ≤ ε * (a0 + a1) * Sb := by
      rw [sqNorm_eq_dot]
      conv_lhs => arg 2; rw [hWsum]
      rw [dotProduct_neg, dotProduct_sum, Matrix.mulVec_add]
      simp only [add_dotProduct]
      rw [hSb, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have i0 := rip_inner_le hW u0 (r j) hl0u0 (hl0r j) (hdisj0r j)
      have i1 := rip_inner_le hW u1 (r j) hl0u1 (hl0r j) (hdisj1r j)
      have := neg_abs_le ((W.mulVec u0) ⬝ᵥ (W.mulVec (r j)))
      have := neg_abs_le ((W.mulVec u1) ⬝ᵥ (W.mulVec (r j)))
      simp only [hb]
      nlinarith
    have hsum2 : a0 + a1 ≤ Real.sqrt 2 * A := by
      have h0 : 0 ≤ a0 := nrm_nonneg _
      have h1 : 0 ≤ a1 := nrm_nonneg _
      have hA0 : 0 ≤ A := nrm_nonneg _
      rw [show Real.sqrt 2 * A = Real.sqrt (2 * A ^ 2) by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hA0]]
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (a0 - a1)]
    have hSb0 : 0 ≤ Sb := Finset.sum_nonneg (fun j _ => nrm_nonneg _)
    calc (1 - ε) * A ^ 2 ≤ sqNorm (W.mulVec (u0 + u1)) := hlow
      _ ≤ ε * (a0 + a1) * Sb := hsq
      _ ≤ ε * (Real.sqrt 2 * A) * Sb := by
          apply mul_le_mul_of_nonneg_right _ hSb0
          exact mul_le_mul_of_nonneg_left hsum2 hε0
      _ = Real.sqrt 2 * ε * A * Sb := by ring
  have hfinal := final_arith ε e A Sb L a0 (nrm h) (Real.sqrt s) hSpos hε0 hε (nrm_nonneg _)
    (Finset.sum_nonneg (fun j _ => nrm_nonneg _)) F1 F2 F3 F4 F5
  have hrpow : (s : ℝ) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt s := by
    rw [Real.sqrt_eq_rpow, neg_div, Real.rpow_neg hsR.le, one_div, one_div]
  rw [hrpow]
  exact hfinal
