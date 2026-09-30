-- Prove2me | solution 1 for UnderstandingML.binary_uc_optimal_rate
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T05:58:08.551173+00:00
-- url     : https://prove2.me/submissions/8524d61b-7a54-41d5-9a41-cab04a61bbb6

import Definitions.Def_UnderstandingML_VC
import Mathlib

open MeasureTheory

universe u

-- ===== UCMassart =====

/-!
# Rademacher averages over sign vectors and Massart's finite-class lemma

Everything here is a finite average over the `2^m` sign vectors `σ : Fin m → Bool`.
-/

open Real

namespace UCOpt

/-- The sign `±1` encoded by a boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Average of `F` over all sign vectors. -/
noncomputable def savg (m : ℕ) (F : (Fin m → Bool) → ℝ) : ℝ := (∑ σ, F σ) / 2 ^ m

/-- The correlation `∑ᵢ σᵢ aᵢ`. -/
def corr {m : ℕ} (σ : Fin m → Bool) (a : Fin m → ℝ) : ℝ := ∑ i, sgn (σ i) * a i

/-- The squared Euclidean norm `∑ᵢ aᵢ²`. -/
def sqn {m : ℕ} (a : Fin m → ℝ) : ℝ := ∑ i, a i ^ 2

lemma card_signs (m : ℕ) : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by
  simp

lemma savg_add {m : ℕ} (F G : (Fin m → Bool) → ℝ) :
    savg m (fun σ ↦ F σ + G σ) = savg m F + savg m G := by
  unfold savg; rw [Finset.sum_add_distrib, add_div]

lemma savg_mono {m : ℕ} {F G : (Fin m → Bool) → ℝ} (h : ∀ σ, F σ ≤ G σ) :
    savg m F ≤ savg m G := by
  unfold savg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ ↦ h σ) (by positivity)

lemma savg_const {m : ℕ} (c : ℝ) : savg m (fun _ ↦ c) = c := by
  unfold savg
  rw [Finset.sum_const, card_signs, nsmul_eq_mul]
  push_cast
  field_simp

lemma savg_sum {m : ℕ} {ι : Type*} (s : Finset ι) (F : ι → (Fin m → Bool) → ℝ) :
    savg m (fun σ ↦ ∑ k ∈ s, F k σ) = ∑ k ∈ s, savg m (F k) := by
  unfold savg
  rw [Finset.sum_comm, Finset.sum_div]

lemma savg_nonneg {m : ℕ} {F : (Fin m → Bool) → ℝ} (h : ∀ σ, 0 ≤ F σ) : 0 ≤ savg m F := by
  unfold savg; exact div_nonneg (Finset.sum_nonneg fun σ _ ↦ h σ) (by positivity)

/-- Jensen's inequality for the exponential and the sign average. -/
lemma exp_savg_le {m : ℕ} (F : (Fin m → Bool) → ℝ) :
    exp (savg m F) ≤ savg m (fun σ ↦ exp (F σ)) := by
  have hw : ∀ σ ∈ (Finset.univ : Finset (Fin m → Bool)), (0 : ℝ) ≤ 1 / 2 ^ m :=
    fun _ _ ↦ by positivity
  have hw1 : ∑ _σ ∈ (Finset.univ : Finset (Fin m → Bool)), (1 : ℝ) / 2 ^ m = 1 := by
    rw [Finset.sum_const, card_signs, nsmul_eq_mul]; push_cast; field_simp
  have := convexOn_exp.map_sum_le hw hw1 (fun σ _ ↦ Set.mem_univ (F σ))
  simp only [smul_eq_mul] at this
  have e1 : savg m F = ∑ σ, 1 / 2 ^ m * F σ := by
    unfold savg; rw [Finset.sum_div]; exact Finset.sum_congr rfl fun σ _ ↦ by ring
  have e2 : savg m (fun σ ↦ exp (F σ)) = ∑ σ, 1 / 2 ^ m * exp (F σ) := by
    unfold savg; rw [Finset.sum_div]; exact Finset.sum_congr rfl fun σ _ ↦ by ring
  rw [e1, e2]; exact this

/-- The moment generating function of a Rademacher sum. -/
lemma savg_exp_corr {m : ℕ} (l : ℝ) (a : Fin m → ℝ) :
    savg m (fun σ ↦ exp (l * corr σ a)) ≤ exp (l ^ 2 * sqn a / 2) := by
  have key : ∑ σ : Fin m → Bool, exp (l * corr σ a) =
      ∏ i, ∑ b : Bool, exp (l * (sgn b * a i)) := by
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [← Real.exp_sum]; unfold corr; rw [Finset.mul_sum]
  unfold savg
  rw [key]
  have h2 : (2 : ℝ) ^ m = ∏ _i : Fin m, (2 : ℝ) := by simp
  rw [h2, ← Finset.prod_div_distrib]
  have h3 : exp (l ^ 2 * sqn a / 2) = ∏ i : Fin m, exp (l ^ 2 * a i ^ 2 / 2) := by
    rw [← Real.exp_sum]; unfold sqn; congr 1
    rw [Finset.mul_sum, Finset.sum_div]
  rw [h3]
  refine Finset.prod_le_prod (fun i _ ↦ by positivity) fun i _ ↦ ?_
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, sgn, if_true]
  simp only [Bool.false_eq_true, if_false]
  have hc := Real.cosh_le_exp_half_sq (l * a i)
  rw [Real.cosh_eq] at hc
  calc (exp (l * (1 * a i)) + exp (l * (-1 * a i))) / 2 = (exp (l * a i) + exp (-(l * a i))) / 2 := by
        ring_nf
    _ ≤ exp ((l * a i) ^ 2 / 2) := hc
    _ = exp (l ^ 2 * a i ^ 2 / 2) := by ring_nf

lemma corr_neg {m : ℕ} (σ : Fin m → Bool) (a : Fin m → ℝ) (l : ℝ) :
    -l * corr σ a = l * corr σ (-a) := by
  unfold corr; simp [Finset.mul_sum]

lemma sqn_neg {m : ℕ} (a : Fin m → ℝ) : sqn (-a) = sqn a := by
  unfold sqn; simp

lemma sqn_nonneg {m : ℕ} (a : Fin m → ℝ) : 0 ≤ sqn a :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma corr_eq_zero_of_sqn {m : ℕ} (σ : Fin m → Bool) {a : Fin m → ℝ} (h : sqn a = 0) :
    corr σ a = 0 := by
  have : ∀ i, a i = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg (a i))).1 h i
      (Finset.mem_univ _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  unfold corr; simp [this]

/-- **Massart's lemma** (selection form): if `φ σ` always lies in the finite set `T` of vectors,
each of squared norm at most `v`, then `E_σ |⟨σ, φ σ⟩| ≤ √(2 v log(2|T|))`. -/
theorem massart {m : ℕ} (T : Finset (Fin m → ℝ)) (φ : (Fin m → Bool) → (Fin m → ℝ))
    (hφ : ∀ σ, φ σ ∈ T) {v : ℝ} (hv0 : 0 ≤ v) (hv : ∀ t ∈ T, sqn t ≤ v) :
    savg m (fun σ ↦ |corr σ (φ σ)|) ≤ sqrt (2 * v * log (2 * T.card)) := by
  have hne : T.Nonempty := ⟨φ (fun _ ↦ true), hφ _⟩
  have hN : (1 : ℝ) ≤ T.card := by exact_mod_cast hne.card_pos
  set L := log (2 * (T.card : ℝ)) with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  rcases hv0.lt_or_eq with hvpos | hv0'
  · set l := sqrt (2 * L / v) with hl
    have hlpos : 0 < l := Real.sqrt_pos.2 (by positivity)
    set A := savg m (fun σ ↦ |corr σ (φ σ)|)
    have h1 : exp (l * A) ≤ 2 * T.card * exp (l ^ 2 * v / 2) := by
      have e1 : l * A = savg m (fun σ ↦ l * |corr σ (φ σ)|) := by
        unfold A savg; rw [mul_div_assoc', Finset.mul_sum]
      rw [e1]
      refine (exp_savg_le _).trans ?_
      have hpt : ∀ σ, exp (l * |corr σ (φ σ)|) ≤
          ∑ t ∈ T, (exp (l * corr σ t) + exp (l * corr σ (-t))) := by
        intro σ
        refine le_trans ?_ (Finset.single_le_sum (f := fun t ↦ exp (l * corr σ t) +
          exp (l * corr σ (-t))) (fun t _ ↦ by positivity) (hφ σ))
        rcases abs_cases (corr σ (φ σ)) with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]; linarith [exp_pos (l * corr σ (-φ σ))]
        · rw [h, show l * -corr σ (φ σ) = l * corr σ (-φ σ) by rw [← corr_neg]; ring]
          try dsimp only
          linarith [exp_pos (l * corr σ (φ σ))]
      refine (savg_mono hpt).trans ?_
      rw [savg_sum]
      calc ∑ t ∈ T, savg m (fun σ ↦ exp (l * corr σ t) + exp (l * corr σ (-t)))
          ≤ ∑ _t ∈ T, 2 * exp (l ^ 2 * v / 2) := by
            refine Finset.sum_le_sum fun t ht ↦ ?_
            rw [savg_add]
            have a1 := savg_exp_corr l t
            have a2 := savg_exp_corr l (-t)
            rw [sqn_neg] at a2
            have b : exp (l ^ 2 * sqn t / 2) ≤ exp (l ^ 2 * v / 2) := by
              gcongr; exact hv t ht
            linarith
        _ = 2 * T.card * exp (l ^ 2 * v / 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
    have h2 : l * A ≤ L + l ^ 2 * v / 2 := by
      have := Real.log_le_log (exp_pos _) h1
      rw [Real.log_exp, Real.log_mul (by positivity) (exp_pos _).ne', Real.log_exp] at this
      exact this
    have hl2 : l ^ 2 = 2 * L / v := Real.sq_sqrt (by positivity)
    have hA : A ≤ L / l + l * v / 2 := by
      rw [div_add' _ _ _ hlpos.ne', le_div_iff₀ hlpos]
      nlinarith
    have hfin : L / l + l * v / 2 = sqrt (2 * v * L) := by
      have hs : sqrt (2 * v * L) = l * v := by
        rw [hl, ← Real.sqrt_sq (le_of_lt (mul_pos hlpos hvpos)), mul_pow, hl2]
        congr 1; field_simp
      rw [hs]
      field_simp
      rw [hl2]; field_simp; ring
    linarith
  · subst hv0'
    have hz : ∀ σ, corr σ (φ σ) = 0 := fun σ ↦
      corr_eq_zero_of_sqn σ (le_antisymm (hv _ (hφ σ)) (sqn_nonneg _))
    simp only [hz, abs_zero, savg_const]
    exact Real.sqrt_nonneg _

end UCOpt

-- ===== UCPacking =====

/-!
# Packing numbers of VC classes in normalized Hamming distance

If a class of VC dimension at most `d` realises a family of patterns on `n` points that are
pairwise at Hamming distance at least `ε n`, the family has at most `exp(d (4 + 2 log(1/ε)))`
members. Consequently every set of patterns has an `ε n`-cover of that size.
-/

open Real UnderstandingML

namespace UCOpt

variable {α : Type*}

/-- Hamming distance between two patterns. -/
def ham {n : ℕ} (p q : Fin n → Bool) : ℕ := (Finset.univ.filter fun j ↦ p j ≠ q j).card

lemma ham_comm {n : ℕ} (p q : Fin n → Bool) : ham p q = ham q p := by
  unfold ham; congr 1; ext j; simp [eq_comm]

lemma ham_self {n : ℕ} (p : Fin n → Bool) : ham p p = 0 := by simp [ham]

lemma ham_le {n : ℕ} (p q : Fin n → Bool) : ham p q ≤ n := by
  unfold ham; exact (Finset.card_filter_le _ _).trans (by simp)

/-- **Sauer–Shelah** for patterns realised by a class of VC dimension at most `d` on the
(possibly repeated) points `y₀, …, y_{k-1}`. -/
theorem card_le_sum_choose (F : Set (α → Bool)) (d : ℕ) (hF : vcDim F ≤ d) {k : ℕ}
    (y : Fin k → α) (R : Finset (Fin k → Bool)) (hR : ∀ r ∈ R, ∃ f ∈ F, ∀ i, r i = f (y i)) :
    R.card ≤ ∑ i ∈ Finset.Iic d, k.choose i := by
  classical
  set supp : (Fin k → Bool) → Finset (Fin k) := fun r ↦ Finset.univ.filter fun i ↦ r i = true
  have hinj : Function.Injective supp := by
    intro r r' h
    funext i
    have := congrArg (fun s ↦ i ∈ s) h
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases hr : r i <;> cases hr' : r' i <;> simp_all
  set 𝒜 := R.image supp
  have hcard : R.card = 𝒜.card := (Finset.card_image_of_injective _ hinj).symm
  have hvc : 𝒜.vcDim ≤ d := by
    unfold Finset.vcDim
    refine Finset.sup_le fun s hs ↦ ?_
    have hsh := Finset.mem_shatterer.1 hs
    -- every sign pattern on `s` is realised by some `r ∈ R`
    have real : ∀ g : Fin k → Bool, ∃ r ∈ R, ∀ i ∈ s, r i = g i := by
      intro g
      obtain ⟨u, hu, hsu⟩ := hsh (Finset.filter_subset (fun i ↦ g i = true) s)
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hu
      refine ⟨r, hr, fun i hi ↦ ?_⟩
      have := congrArg (fun t ↦ i ∈ t) hsu
      simp only [supp, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
        eq_iff_iff] at this
      cases hr : r i <;> cases hg : g i <;> simp_all
    -- the points indexed by `s` are distinct
    have hinjs : Set.InjOn y s := by
      intro i hi i' hi' hyy
      by_contra hne
      obtain ⟨r, hr, hrg⟩ := real (fun j ↦ decide (j = i))
      obtain ⟨f, -, hf⟩ := hR r hr
      have h1 := hrg i hi
      have h2 := hrg i' hi'
      rw [hf, hyy] at h1
      rw [hf, h1] at h2
      simp [Ne.symm hne] at h2
    set C := s.image y
    have hCcard : C.card = s.card := Finset.card_image_of_injOn hinjs
    have hsh' : Shatters F C := by
      intro g
      have : ∀ c ∈ C, ∃ i ∈ s, y i = c := fun c hc ↦ by simpa using Finset.mem_image.1 hc
      obtain ⟨r, hr, hrg⟩ := real (fun i ↦ if h : y i ∈ C then g ⟨y i, h⟩ else false)
      obtain ⟨f, hfF, hf⟩ := hR r hr
      refine ⟨f, hfF, fun c ↦ ?_⟩
      obtain ⟨i, hi, hic⟩ := this c c.2
      have := hrg i hi
      rw [hf] at this
      have hyC : y i ∈ C := Finset.mem_image_of_mem y hi
      rw [dif_pos hyC] at this
      have hc : (⟨y i, hyC⟩ : C) = c := Subtype.ext hic
      rw [← hc]; exact this
    have hle : (C.card : ℕ∞) ≤ vcDim F := le_iSup₂ (f := fun C (_ : Shatters F C) ↦
      (C.card : ℕ∞)) C hsh'
    have : (C.card : ℕ∞) ≤ d := hle.trans hF
    rw [hCcard] at this
    exact_mod_cast this
  calc R.card = 𝒜.card := hcard
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ i ∈ Finset.Iic 𝒜.vcDim, (Fintype.card (Fin k)).choose i :=
        Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ i ∈ Finset.Iic d, k.choose i := by
        rw [Fintype.card_fin]
        exact Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.2 hvc)

lemma sum_choose_mul_le (n d : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ i ∈ Finset.Iic d, (n.choose i : ℝ) * a ^ i ≤ (1 + a) ^ n := by
  rw [add_comm (1 : ℝ) a, add_pow]
  simp only [one_pow, mul_one]
  calc ∑ i ∈ Finset.Iic d, (n.choose i : ℝ) * a ^ i
      = ∑ i ∈ (Finset.Iic d).filter (· ≤ n), (n.choose i : ℝ) * a ^ i := by
        rw [Finset.sum_filter_of_ne]
        intro i _ hi
        by_contra h
        push_neg at h
        rw [Nat.choose_eq_zero_of_lt h] at hi
        simp at hi
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * a ^ i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_range] at hi ⊢
          omega
        · intro i _ _; positivity
    _ = _ := Finset.sum_congr rfl fun i _ ↦ by ring

/-- `∑_{i ≤ d} C(k, i) ≤ (e k / d)^d` for `1 ≤ d ≤ k`. -/
lemma sum_choose_le_pow {k d : ℕ} (hd : 1 ≤ d) (hdk : d ≤ k) :
    (∑ i ∈ Finset.Iic d, (k.choose i : ℝ)) ≤ (exp 1 * k / d) ^ d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hd hdk)
  set a : ℝ := d / k
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hdk) hkpos.le
  have h1 : a ^ d * ∑ i ∈ Finset.Iic d, (k.choose i : ℝ) ≤
      ∑ i ∈ Finset.Iic d, (k.choose i : ℝ) * a ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ha0 ha1 (Finset.mem_Iic.1 hi))
      (by positivity)
  have h2 : (1 + a) ^ k ≤ exp 1 ^ d := by
    have := Real.add_one_le_exp a
    calc (1 + a) ^ k ≤ exp a ^ k := by gcongr; linarith
      _ = exp (a * k) := by rw [← Real.exp_nat_mul]; ring_nf
      _ = exp 1 ^ d := by
        rw [← Real.exp_nat_mul]; congr 1; unfold a; field_simp
  have h3 := (h1.trans (sum_choose_mul_le k d ha0)).trans h2
  have hapos : 0 < a ^ d := by positivity
  rw [mul_comm, ← le_div_iff₀ hapos] at h3
  refine h3.trans (le_of_eq ?_)
  unfold a
  rw [div_pow, div_pow, mul_pow]
  field_simp

lemma log_one_add_two_mul_le {x : ℝ} (hx : 0 ≤ x) : log (1 + 2 * x) ≤ x / 2 + 1 := by
  have h4 : log (1 + 2 * x) = log ((1 + 2 * x) / 4) + log 4 := by
    rw [Real.log_div (by positivity) (by norm_num)]; ring
  have h5 := Real.log_le_sub_one_of_pos (show 0 < (1 + 2 * x) / 4 by positivity)
  have h6 : log 4 < 1.39 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; have := Real.log_two_lt_d9; push_cast; linarith
  linarith

/-- The key numerical step: if `L ≤ d (1 + log(k/d))` with `k ≤ 2L/ε + 1`, then
`L ≤ d (4 + 2 log (1/ε))`. -/
lemma packing_numeric {L ε : ℝ} {d k : ℕ} (hd : 1 ≤ d) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hk : (k : ℝ) ≤ 2 * L / ε + 1) (hdk : d ≤ k) (hLk : L ≤ d * (1 + log (k / d))) :
    L ≤ d * (4 + 2 * log (1 / ε)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set x := L / d with hx
  have hx0 : 0 ≤ x := by positivity
  have hLx : L = d * x := by rw [hx]; field_simp
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le hd hdk)
  have hkd : (k : ℝ) / d ≤ (1 + 2 * x) / ε := by
    rw [div_le_div_iff₀ hdpos hε]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have : (k : ℝ) * ε ≤ 2 * L + ε := by
      have := mul_le_mul_of_nonneg_right hk hε.le
      rwa [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at this
    rw [hLx] at this
    nlinarith
  have hlog : log (k / d) ≤ log (1 + 2 * x) + log (1 / ε) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by rw [mul_one_div]; exact hkd)
  have hx2 : x ≤ 1 + log (k / d) := by
    rw [hLx] at hLk
    exact le_of_mul_le_mul_left hLk hdpos
  have := log_one_add_two_mul_le hx0
  have hfin : x ≤ 4 + 2 * log (1 / ε) := by linarith
  rw [hLx]
  exact mul_le_mul_of_nonneg_left hfin hdpos.le

/-- **Packing bound.** A family of patterns realised by a class of VC dimension at most `d ≥ 1`
on `n` points, pairwise at Hamming distance at least `ε n`, has at most
`exp(d (4 + 2 log(1/ε)))` members. -/
theorem packing_bound (F : Set (α → Bool)) (d : ℕ) (hd : 1 ≤ d) (hF : vcDim F ≤ d) {n : ℕ}
    (w : Fin n → α) (Q : Finset (Fin n → Bool)) (hQ : ∀ q ∈ Q, ∃ f ∈ F, ∀ j, q j = f (w j))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsep : ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → ε * n ≤ ham q q') :
    log Q.card ≤ d * (4 + 2 * log (1 / ε)) := by
  classical
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hRHS : 0 ≤ d * (4 + 2 * log (1 / ε)) := by
    have : 0 ≤ log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    positivity
  rcases le_or_gt Q.card 1 with hQ1 | hQ1
  · have : log (Q.card : ℝ) ≤ 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hQ1 with h | h <;> simp [h]
    linarith
  -- `n ≥ 1`, otherwise all patterns coincide
  have hn : 1 ≤ n := by
    by_contra hn0
    push_neg at hn0
    interval_cases n
    obtain ⟨q, hq, q', hq', hne⟩ := Finset.one_lt_card.1 hQ1
    exact hne (funext fun j ↦ j.elim0)
  set N := Q.card
  set L := log (N : ℝ) with hLdef
  have hNpos : (1 : ℝ) < N := by exact_mod_cast hQ1
  have hL0 : 0 < L := Real.log_pos hNpos
  set k := ⌊2 * L / ε⌋₊ + 1 with hkdef
  have hk1 : 2 * L / ε < k := by rw [hkdef]; push_cast; exact Nat.lt_floor_add_one _
  have hk2 : (k : ℝ) ≤ 2 * L / ε + 1 := by
    rw [hkdef]; push_cast; linarith [Nat.floor_le (show 0 ≤ 2 * L / ε by positivity)]
  -- counting colliding pairs over all position tuples
  set pairs := Q.offDiag
  set coll : (Fin k → Fin n) → (Fin n → Bool) × (Fin n → Bool) → Prop :=
    fun J pq ↦ ∀ i, pq.1 (J i) = pq.2 (J i)
  have hcount : ∑ J : Fin k → Fin n, (pairs.filter (coll J)).card < (n : ℝ) ^ k := by
    have hswap : ∑ J : Fin k → Fin n, ((pairs.filter (coll J)).card : ℝ) =
        ∑ pq ∈ pairs, ((Finset.univ.filter fun J ↦ coll J pq).card : ℝ) := by
      simp only [Finset.card_filter]
      push_cast
      exact Finset.sum_comm
    push_cast
    rw [hswap]
    have hpair : ∀ pq ∈ pairs, ((Finset.univ.filter fun J ↦ coll J pq).card : ℝ) ≤
        ((1 - ε) * n) ^ k := by
      intro pq hpq
      obtain ⟨hp, hq, hne⟩ := Finset.mem_offDiag.1 hpq
      set A := Finset.univ.filter fun j : Fin n ↦ pq.1 j = pq.2 j
      have hAeq : (Finset.univ.filter fun J ↦ coll J pq) = Fintype.piFinset fun _ ↦ A := by
        ext J; simp [coll, A, Fintype.mem_piFinset]
      rw [hAeq, Fintype.card_piFinset]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      push_cast
      gcongr
      have hsum : (A.card : ℝ) + ham pq.1 pq.2 = n := by
        unfold ham
        have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
          (fun j : Fin n ↦ pq.1 j = pq.2 j)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this
      have := hsep _ hp _ hq hne
      linarith
    calc ∑ pq ∈ pairs, ((Finset.univ.filter fun J ↦ coll J pq).card : ℝ)
        ≤ ∑ _pq ∈ pairs, ((1 - ε) * n) ^ k := Finset.sum_le_sum hpair
      _ ≤ (N : ℝ) ^ 2 * ((1 - ε) * n) ^ k := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have h1e : 0 ≤ 1 - ε := by linarith
          have hpc : (pairs.card : ℝ) ≤ (N : ℝ) ^ 2 := by
            have : pairs.card ≤ N * N := by
              rw [Finset.offDiag_card]; exact Nat.sub_le _ _
            calc (pairs.card : ℝ) ≤ (N * N : ℕ) := by exact_mod_cast this
              _ = (N : ℝ) ^ 2 := by push_cast; ring
          exact mul_le_mul_of_nonneg_right hpc
            (pow_nonneg (mul_nonneg h1e (Nat.cast_nonneg _)) _)
      _ < (n : ℝ) ^ k := by
          rw [mul_pow, ← mul_assoc]
          have hnk : (0 : ℝ) < (n : ℝ) ^ k := by
            have : (0 : ℝ) < n := by exact_mod_cast hn
            positivity
          have hlt : (N : ℝ) ^ 2 * (1 - ε) ^ k < 1 := by
            have e1 : (1 - ε) ^ k ≤ exp (-(ε * k)) := by
              calc (1 - ε) ^ k ≤ exp (-ε) ^ k :=
                    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-ε)]) k
                _ = exp (-(ε * k)) := by rw [← Real.exp_nat_mul]; ring_nf
            have e2 : exp (-(ε * k)) < exp (-(2 * L)) := by
              apply Real.exp_lt_exp.2
              have := (div_lt_iff₀ hε).1 hk1
              linarith
            have e3 : (N : ℝ) ^ 2 * exp (-(2 * L)) = 1 := by
              rw [show -(2 * L) = -(2 * L) from rfl, Real.exp_neg, show 2 * L = L + L by ring,
                Real.exp_add, hLdef, Real.exp_log (by linarith)]
              field_simp
            calc (N : ℝ) ^ 2 * (1 - ε) ^ k ≤ (N : ℝ) ^ 2 * exp (-(ε * k)) := by gcongr
              _ < (N : ℝ) ^ 2 * exp (-(2 * L)) := by gcongr
              _ = 1 := e3
          calc (N : ℝ) ^ 2 * (1 - ε) ^ k * (n : ℝ) ^ k < 1 * (n : ℝ) ^ k := by gcongr
            _ = _ := one_mul _
  -- hence some tuple has no colliding pair
  obtain ⟨J, hJ⟩ : ∃ J : Fin k → Fin n, (pairs.filter (coll J)).card = 0 := by
    by_contra hall
    push_neg at hall
    have : ∀ J : Fin k → Fin n, (1 : ℝ) ≤ (pairs.filter (coll J)).card := fun J ↦ by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (hall J)
    have := Finset.sum_le_sum fun J (_ : J ∈ Finset.univ) ↦ this J
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at this
    push_cast at this hcount
    linarith
  have hinj : Set.InjOn (fun q : Fin n → Bool ↦ fun i ↦ q (J i)) Q := by
    intro q hq q' hq' heq
    by_contra hne
    have hmem : (q, q') ∈ pairs.filter (coll J) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_offDiag.2 ⟨hq, hq', hne⟩, fun i ↦ ?_⟩
      exact congrFun heq i
    rw [Finset.card_eq_zero] at hJ
    rw [hJ] at hmem
    simp at hmem
  set R := Q.image fun q : Fin n → Bool ↦ fun i ↦ q (J i)
  have hRcard : R.card = N := Finset.card_image_of_injOn hinj
  have hRsauer := card_le_sum_choose F d hF (w ∘ J) R (by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨f, hf, hfq⟩ := hQ q hq
    exact ⟨f, hf, fun i ↦ hfq (J i)⟩)
  rw [hRcard] at hRsauer
  -- enlarge `k` to `k' = max k d`
  set k' := max k d
  have hNle : (N : ℝ) ≤ (exp 1 * k' / d) ^ d := by
    have h1 : (N : ℝ) ≤ ∑ i ∈ Finset.Iic d, (k.choose i : ℝ) := by exact_mod_cast hRsauer
    have h2 : ∑ i ∈ Finset.Iic d, (k.choose i : ℝ) ≤ ∑ i ∈ Finset.Iic d, (k'.choose i : ℝ) := by
      gcongr with i
      exact le_max_left _ _
    exact h1.trans (h2.trans (sum_choose_le_pow hd (le_max_right _ _)))
  have hLle : L ≤ d * (1 + log (k' / d)) := by
    have hk'pos : (0 : ℝ) < k' := by
      have : 1 ≤ k' := le_trans hd (le_max_right _ _)
      exact_mod_cast this
    have := Real.log_le_log (by linarith) hNle
    rw [Real.log_pow, mul_div_assoc, Real.log_mul (exp_pos 1).ne' (by positivity),
      Real.log_exp] at this
    exact this
  rcases le_total k d with hkd | hkd
  · have hk' : k' = d := max_eq_right hkd
    rw [hk'] at hLle
    have : (d : ℝ) / d = 1 := div_self hdpos.ne'
    rw [this, Real.log_one, add_zero, mul_one] at hLle
    have : 0 ≤ log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    nlinarith
  · have hk' : k' = k := max_eq_left hkd
    rw [hk'] at hLle
    exact packing_numeric hd hL0.le hε hε1 hk2 hkd hLle

/-- **Covering.** Every family of patterns realised by a class of VC dimension at most `d ≥ 1`
on `n ≥ 1` points has, for each `ε ∈ (0, 1]`, a subfamily of at most
`exp(d (4 + 2 log(1/ε)))` members within Hamming distance `< ε n` of every member. -/
theorem exists_cover (F : Set (α → Bool)) (d : ℕ) (hd : 1 ≤ d) (hF : vcDim F ≤ d) {n : ℕ}
    (hn : 1 ≤ n) (w : Fin n → α) (P : Finset (Fin n → Bool))
    (hP : ∀ p ∈ P, ∃ f ∈ F, ∀ j, p j = f (w j)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N ⊆ P, (N.card : ℝ) ≤ exp (d * (4 + 2 * log (1 / ε))) ∧
      ∀ p ∈ P, ∃ q ∈ N, (ham p q : ℝ) < ε * n := by
  classical
  set Sep : Finset (Fin n → Bool) → Prop :=
    fun Q ↦ ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → ε * n ≤ ham q q'
  set cands := P.powerset.filter Sep
  have hne : cands.Nonempty := ⟨∅, by simp [cands, Sep]⟩
  obtain ⟨N, hN, hmax⟩ := cands.exists_max_image Finset.card hne
  obtain ⟨hNP, hNsep⟩ := Finset.mem_filter.1 hN
  rw [Finset.mem_powerset] at hNP
  refine ⟨N, hNP, ?_, ?_⟩
  · have hb := packing_bound F d hd hF w N (fun q hq ↦ hP q (hNP hq)) hε hε1 hNsep
    rcases Nat.eq_zero_or_pos N.card with h0 | hpos
    · rw [h0]; simp; positivity
    · have : (0 : ℝ) < N.card := by exact_mod_cast hpos
      rw [← Real.exp_log this]
      exact Real.exp_le_exp.2 hb
  · intro p hp
    by_contra hfar
    push_neg at hfar
    have hpN : p ∉ N := by
      intro hpN
      have := hfar p hpN
      simp only [ham_self, Nat.cast_zero] at this
      have : (0 : ℝ) < ε * n := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      linarith
    have hins : insert p N ∈ cands := by
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset hp hNP), ?_⟩
      intro q hq q' hq' hqq'
      rcases Finset.mem_insert.1 hq with h1 | hq <;>
        rcases Finset.mem_insert.1 hq' with h2 | hq'
      · exact absurd (h1.trans h2.symm) hqq'
      · rw [h1]; exact hfar q' hq'
      · rw [h2, ham_comm]; exact hfar q hq
      · exact hNsep q hq q' hq' hqq'
    have := hmax _ hins
    rw [Finset.card_insert_of_notMem hpN] at this
    omega

end UCOpt

-- ===== UCChaining =====

/-!
# Dudley-type chaining over a finite family of patterns

Given vectors `a p ∈ ℝ^m` indexed by patterns `p ∈ P`, whose pairwise squared distances are
controlled by Hamming distances of the patterns, and Hamming covers of size
`exp(d (4 + 2 log 4^k))` at scale `n/4^k`, the Rademacher average of `max_p |⟨σ, a p⟩|` is
`O(√m + √(n d))`.
-/

open Real

namespace UCOpt

lemma corr_sub {m : ℕ} (σ : Fin m → Bool) (x y : Fin m → ℝ) :
    corr σ (x - y) = corr σ x - corr σ y := by
  unfold corr; rw [← Finset.sum_sub_distrib]; simp [mul_sub]

lemma sqn_add_le {m : ℕ} (x y : Fin m → ℝ) : sqn (x + y) ≤ 2 * sqn x + 2 * sqn y := by
  unfold sqn; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  simp only [Pi.add_apply]; nlinarith [sq_nonneg (x i - y i)]

lemma sqn_sub_comm {m : ℕ} (x y : Fin m → ℝ) : sqn (x - y) = sqn (y - x) := by
  rw [← neg_sub, sqn_neg]

lemma sum_link_weights (K : ℕ) :
    ∑ k ∈ Finset.range K, ((k : ℝ) + 4) / 2 ^ (k + 1) = 5 - ((K : ℝ) + 5) / 2 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

lemma link_bound (k n d : ℕ) {v L : ℝ}
    (hv : v ≤ 20 * n / 4 ^ (k + 1)) (hL0 : 0 ≤ L) (hL : L ≤ d * (15 + 6 * k)) :
    sqrt (2 * v * L) ≤ ((k : ℝ) + 4) / 2 ^ (k + 1) * sqrt (40 * n * d) := by
  have h4 : (4 : ℝ) ^ (k + 1) = (2 ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have hpos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  rw [show ((k : ℝ) + 4) / 2 ^ (k + 1) * sqrt (40 * n * d) =
      sqrt ((((k : ℝ) + 4) / 2 ^ (k + 1)) ^ 2 * (40 * n * d)) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc 2 * v * L ≤ 2 * (20 * n / 4 ^ (k + 1)) * (d * (15 + 6 * k)) := by
        gcongr
    _ ≤ (((k : ℝ) + 4) / 2 ^ (k + 1)) ^ 2 * (40 * n * d) := by
        rw [h4, div_pow]
        rw [div_mul_eq_mul_div, mul_div_assoc', div_mul_eq_mul_div, div_le_div_iff_of_pos_right
          (by positivity)]
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith [mul_nonneg hn hdd, mul_nonneg (mul_nonneg hn hdd) (sq_nonneg (k : ℝ))]

lemma log_four_lt : log 4 < 1.3863 := by
  have : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [this, Real.log_pow]; have := Real.log_two_lt_d9; push_cast; linarith

/-- **Chaining.** -/
theorem chaining {m n d : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (P : Finset (Fin n → Bool))
    (a : (Fin n → Bool) → (Fin m → ℝ))
    (ha1 : ∀ p ∈ P, sqn (a p) ≤ m)
    (ha2 : ∀ p ∈ P, ∀ q ∈ P, sqn (a p - a q) ≤ 2 * ham p q)
    (hcov : ∀ k : ℕ, ∃ N ⊆ P, (N.card : ℝ) ≤ exp (d * (4 + 2 * log (4 ^ (k + 1)))) ∧
      ∀ p ∈ P, ∃ q ∈ N, (ham p q : ℝ) < n / 4 ^ (k + 1))
    (φ : (Fin m → Bool) → (Fin n → Bool)) (hφ : ∀ σ, φ σ ∈ P) :
    savg m (fun σ ↦ |corr σ (a (φ σ))|) ≤ sqrt (2 * m) + 5 * sqrt (40 * n * d) := by
  classical
  choose N hNP hNcard hNcov using hcov
  set p0 := φ (fun _ ↦ true)
  have hp0 : p0 ∈ P := hφ _
  -- the chain of approximations
  let lev : ℕ → (Fin n → Bool) → (Fin n → Bool) := fun k p ↦
    match k with
    | 0 => p0
    | k + 1 => if hp : p ∈ P then Classical.choose (hNcov k p hp) else p
  let M : ℕ → Finset (Fin n → Bool) := fun k ↦
    match k with
    | 0 => {p0}
    | k + 1 => N k
  have hlevM : ∀ k, ∀ p ∈ P, lev k p ∈ M k := by
    intro k p hp
    cases k with
    | zero => simp [lev, M]
    | succ k =>
      simp only [lev, M, dif_pos hp]
      exact (Classical.choose_spec (hNcov k p hp)).1
  have hlevP : ∀ k, ∀ p ∈ P, lev k p ∈ P := by
    intro k p hp
    cases k with
    | zero => exact hp0
    | succ k => exact hNP k (hlevM (k + 1) p hp)
  have hlevham : ∀ k, ∀ p ∈ P, (ham p (lev (k + 1) p) : ℝ) < n / 4 ^ (k + 1) := by
    intro k p hp
    simp only [lev, dif_pos hp]
    exact (Classical.choose_spec (hNcov k p hp)).2
  have hBpos : ∀ k : ℕ, 0 ≤ (d : ℝ) * (4 + 2 * log (4 ^ k)) := by
    intro k
    have : 0 ≤ log ((4 : ℝ) ^ k) := Real.log_nonneg (one_le_pow₀ (by norm_num))
    positivity
  have hMcard : ∀ k, (M k).card ≤ exp (d * (4 + 2 * log (4 ^ k))) := by
    intro k
    cases k with
    | zero =>
      simp only [M, Finset.card_singleton, Nat.cast_one]
      exact Real.one_le_exp (hBpos 0)
    | succ k => exact hNcard k
  have hdist : ∀ k, ∀ p ∈ P, sqn (a p - a (lev k p)) ≤ 2 * n / 4 ^ k := by
    intro k p hp
    refine (ha2 p hp _ (hlevP k p hp)).trans ?_
    cases k with
    | zero =>
      simp only [pow_zero, div_one]
      have := ham_le p (lev 0 p)
      have : (ham p (lev 0 p) : ℝ) ≤ n := by exact_mod_cast this
      linarith
    | succ k =>
      have := hlevham k p hp
      rw [mul_div_assoc]
      linarith
  -- link sets
  let link : ℕ → (Fin n → Bool) → (Fin m → ℝ) := fun k p ↦ a (lev (k + 1) p) - a (lev k p)
  let T : ℕ → Finset (Fin m → ℝ) := fun k ↦ P.image (link k)
  have hTsub : ∀ k, T k ⊆ (M (k + 1) ×ˢ M k).image (fun qq ↦ a qq.1 - a qq.2) := by
    intro k t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
    exact Finset.mem_image.2 ⟨(lev (k + 1) p, lev k p),
      Finset.mem_product.2 ⟨hlevM (k + 1) p hp, hlevM k p hp⟩, rfl⟩
  have hTcard : ∀ k, ((T k).card : ℝ) ≤ exp (d * (4 + 2 * log (4 ^ (k + 1)))) *
      exp (d * (4 + 2 * log (4 ^ k))) := by
    intro k
    have h1 := Finset.card_le_card (hTsub k)
    have h2 := Finset.card_image_le (s := M (k + 1) ×ˢ M k) (f := fun qq ↦ a qq.1 - a qq.2)
    rw [Finset.card_product] at h2
    have h3 : ((T k).card : ℝ) ≤ (M (k + 1)).card * (M k).card := by
      exact_mod_cast h1.trans h2
    exact h3.trans (mul_le_mul (hMcard (k + 1)) (hMcard k) (by positivity) (by positivity))
  have hTsqn : ∀ k, ∀ t ∈ T k, sqn t ≤ 20 * n / 4 ^ (k + 1) := by
    intro k t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
    have e : link k p = (a (lev (k + 1) p) - a p) + (a p - a (lev k p)) := by
      simp only [link]; abel
    rw [e]
    refine (sqn_add_le _ _).trans ?_
    rw [sqn_sub_comm]
    have h1 := hdist (k + 1) p hp
    have h2 := hdist k p hp
    have : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by ring
    rw [this] at h1 ⊢
    have h4 : (0 : ℝ) < 4 ^ k := by positivity
    have h1' : sqn (a p - a (lev (k + 1) p)) * (4 * 4 ^ k) ≤ 2 * n :=
      (le_div_iff₀ (by positivity)).1 h1
    have h2' : sqn (a p - a (lev k p)) * 4 ^ k ≤ 2 * n := (le_div_iff₀ h4).1 h2
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- the telescoping decomposition
  obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨n - 1, by omega⟩
  have hexact : ∀ σ, ∀ p ∈ P, corr σ (a p - a (lev (K + 1) p)) = 0 := by
    intro σ p hp
    apply corr_eq_zero_of_sqn
    have hh := hlevham K p hp
    have hlt : ((K + 1 : ℕ) : ℝ) / 4 ^ (K + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : K + 1 < 4 ^ (K + 1) := Nat.lt_pow_self (by norm_num)
      exact_mod_cast this.le
    have h0 : ham p (lev (K + 1) p) = 0 := by
      have : (ham p (lev (K + 1) p) : ℝ) < 1 := lt_of_lt_of_le hh hlt
      exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
    have := ha2 p hp _ (hlevP (K + 1) p hp)
    rw [h0, Nat.cast_zero, mul_zero] at this
    exact le_antisymm this (sqn_nonneg _)
  have htele : ∀ σ, ∀ p ∈ P, |corr σ (a p)| ≤ |corr σ (a p0)| +
      ∑ k ∈ Finset.range (K + 1), |corr σ (link k p)| := by
    intro σ p hp
    have hsum : ∑ k ∈ Finset.range (K + 1), corr σ (link k p) =
        corr σ (a (lev (K + 1) p)) - corr σ (a (lev 0 p)) := by
      simp only [link, corr_sub]
      exact Finset.sum_range_sub (fun k ↦ corr σ (a (lev k p))) (K + 1)
    have hsplit : corr σ (a p) = corr σ (a p0) +
        ∑ k ∈ Finset.range (K + 1), corr σ (link k p) + corr σ (a p - a (lev (K + 1) p)) := by
      rw [hsum, corr_sub]; simp only [lev]; ring
    rw [hsplit, hexact σ p hp, add_zero]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
  -- apply Massart to every term
  have hm1 : savg m (fun σ ↦ |corr σ (a p0)|) ≤ sqrt (2 * m) := by
    have := massart {a p0} (fun _ ↦ a p0) (fun _ ↦ Finset.mem_singleton_self _)
      (Nat.cast_nonneg m) (fun t ht ↦ by rw [Finset.mem_singleton.1 ht]; exact ha1 p0 hp0)
    refine this.trans (Real.sqrt_le_sqrt ?_)
    rw [Finset.card_singleton, Nat.cast_one, mul_one]
    have : log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    have hm : (0 : ℝ) ≤ 2 * m := by positivity
    nlinarith
  have hlink : ∀ k, savg m (fun σ ↦ |corr σ (link k (φ σ))|) ≤
      ((k : ℝ) + 4) / 2 ^ (k + 1) * sqrt (40 * ((K + 1 : ℕ) : ℝ) * d) := by
    intro k
    have hmass := massart (T k) (fun σ ↦ link k (φ σ))
      (fun σ ↦ Finset.mem_image_of_mem _ (hφ σ)) (by positivity) (hTsqn k)
    refine hmass.trans ?_
    have hTne : 1 ≤ (T k).card :=
      Finset.card_pos.2 ⟨_, Finset.mem_image_of_mem (link k) hp0⟩
    have hT1 : (1 : ℝ) ≤ (T k).card := by exact_mod_cast hTne
    apply link_bound k (K + 1) d le_rfl
      (Real.log_nonneg (by linarith))
    have hlog : log (2 * (T k).card) ≤ log 2 + (d * (4 + 2 * log (4 ^ (k + 1))) +
        d * (4 + 2 * log (4 ^ k))) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have := Real.log_le_log (by linarith) (hTcard k)
      rw [← Real.exp_add, Real.log_exp] at this
      linarith
    refine hlog.trans ?_
    rw [Real.log_pow, Real.log_pow]
    have h4 := log_four_lt
    have h40 : 0 ≤ log (4 : ℝ) := Real.log_nonneg (by norm_num)
    have h2 : log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ d) hk, mul_nonneg (mul_nonneg
      (by linarith : (0 : ℝ) ≤ d) hk) h40, mul_nonneg (by linarith : (0 : ℝ) ≤ d) h40]
  calc savg m (fun σ ↦ |corr σ (a (φ σ))|)
      ≤ savg m (fun σ ↦ |corr σ (a p0)| +
          ∑ k ∈ Finset.range (K + 1), |corr σ (link k (φ σ))|) :=
        savg_mono fun σ ↦ htele σ (φ σ) (hφ σ)
    _ = savg m (fun σ ↦ |corr σ (a p0)|) +
          ∑ k ∈ Finset.range (K + 1), savg m (fun σ ↦ |corr σ (link k (φ σ))|) := by
        rw [savg_add, savg_sum]
    _ ≤ sqrt (2 * m) + ∑ k ∈ Finset.range (K + 1),
          ((k : ℝ) + 4) / 2 ^ (k + 1) * sqrt (40 * ((K + 1 : ℕ) : ℝ) * d) :=
        add_le_add hm1 (Finset.sum_le_sum fun k _ ↦ hlink k)
    _ ≤ sqrt (2 * m) + 5 * sqrt (40 * ((K + 1 : ℕ) : ℝ) * d) := by
        rw [← Finset.sum_mul, sum_link_weights]
        gcongr
        have : 0 ≤ (((K + 1 : ℕ) : ℝ) + 5) / 2 ^ (K + 1) := by positivity
        linarith

end UCOpt

-- ===== UCRademacherVC =====

/-!
# Rademacher averages of VC classes on a double sample

For a class `H` of VC dimension at most `d ≥ 1` and a double sample `(zᵢ, z'ᵢ)_{i < m}`,
`E_σ sup_{h ∈ H} |∑ᵢ σᵢ (ℓ(h, zᵢ) − ℓ(h, z'ᵢ))| ≤ 47 √(d m)` (in selection form).
-/

open Real UnderstandingML

namespace UCOpt

/-- The 0–1 loss of a predicted bit against a label. -/
def bitLoss (b y : Bool) : ℝ := if b = y then 0 else 1

lemma bitLoss_sub_sq_le (b c y : Bool) :
    (bitLoss b y - bitLoss c y) ^ 2 ≤ if b ≠ c then 1 else 0 := by
  cases b <;> cases c <;> cases y <;> norm_num [bitLoss]

lemma bitLoss_sub_sq_le_one (b y b' y' : Bool) : (bitLoss b y - bitLoss b' y') ^ 2 ≤ 1 := by
  cases b <;> cases y <;> cases b' <;> cases y' <;> norm_num [bitLoss]

lemma ham_eq_sum {n : ℕ} (p q : Fin n → Bool) :
    (ham p q : ℝ) = ∑ j, (if p j ≠ q j then (1 : ℝ) else 0) := by
  unfold ham; rw [Finset.card_filter]; push_cast; rfl

lemma mul_sqrt_eq (c x : ℝ) (hc : 0 ≤ c) : c * sqrt x = sqrt (c ^ 2 * x) := by
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- **Rademacher bound for VC classes on a double sample** (selection form). -/
theorem rademacher_vc {X : Type*} (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hH : vcDim H ≤ d) {m : ℕ} (hm : 1 ≤ m) (W : Fin m → (X × Bool) × (X × Bool))
    (φ : (Fin m → Bool) → (X → Bool)) (hφ : ∀ σ, φ σ ∈ H) :
    savg m (fun σ ↦ |∑ i, sgn (σ i) * (loss01 (φ σ) (W i).1 - loss01 (φ σ) (W i).2)|) ≤
      47 * sqrt (d * m) := by
  classical
  set w : Fin (m + m) → X := Fin.append (fun i ↦ (W i).1.1) (fun i ↦ (W i).2.1)
  set pat : (X → Bool) → (Fin (m + m) → Bool) := fun h j ↦ h (w j)
  set P : Finset (Fin (m + m) → Bool) := Finset.univ.image fun σ ↦ pat (φ σ)
  set a : (Fin (m + m) → Bool) → (Fin m → ℝ) := fun p i ↦
    bitLoss (p (Fin.castAdd m i)) (W i).1.2 - bitLoss (p (Fin.natAdd m i)) (W i).2.2
  have hPreal : ∀ p ∈ P, ∃ f ∈ H, ∀ j, p j = f (w j) := by
    intro p hp
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨φ σ, hφ σ, fun j ↦ rfl⟩
  have hn : 1 ≤ m + m := by omega
  have ha1 : ∀ p ∈ P, sqn (a p) ≤ m := by
    intro p _
    unfold sqn
    calc ∑ i, a p i ^ 2 ≤ ∑ _i : Fin m, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ bitLoss_sub_sq_le_one _ _ _ _
      _ = m := by simp
  have ha2 : ∀ p ∈ P, ∀ q ∈ P, sqn (a p - a q) ≤ 2 * ham p q := by
    intro p _ q _
    rw [ham_eq_sum, Fin.sum_univ_add, mul_add, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    unfold sqn
    refine Finset.sum_le_sum fun i _ ↦ ?_
    simp only [Pi.sub_apply, a]
    have e : bitLoss (p (Fin.castAdd m i)) (W i).1.2 - bitLoss (p (Fin.natAdd m i)) (W i).2.2 -
        (bitLoss (q (Fin.castAdd m i)) (W i).1.2 - bitLoss (q (Fin.natAdd m i)) (W i).2.2) =
        (bitLoss (p (Fin.castAdd m i)) (W i).1.2 - bitLoss (q (Fin.castAdd m i)) (W i).1.2) -
        (bitLoss (p (Fin.natAdd m i)) (W i).2.2 - bitLoss (q (Fin.natAdd m i)) (W i).2.2) := by
      ring
    rw [e]
    have h1 := bitLoss_sub_sq_le (p (Fin.castAdd m i)) (q (Fin.castAdd m i)) (W i).1.2
    have h2 := bitLoss_sub_sq_le (p (Fin.natAdd m i)) (q (Fin.natAdd m i)) (W i).2.2
    nlinarith [sq_nonneg ((bitLoss (p (Fin.castAdd m i)) (W i).1.2 -
      bitLoss (q (Fin.castAdd m i)) (W i).1.2) + (bitLoss (p (Fin.natAdd m i)) (W i).2.2 -
      bitLoss (q (Fin.natAdd m i)) (W i).2.2))]
  have hcov : ∀ k : ℕ, ∃ N ⊆ P, (N.card : ℝ) ≤ exp (d * (4 + 2 * log (4 ^ (k + 1)))) ∧
      ∀ p ∈ P, ∃ q ∈ N, (ham p q : ℝ) < ((m + m : ℕ) : ℝ) / 4 ^ (k + 1) := by
    intro k
    obtain ⟨N, hNP, hNc, hNcov⟩ := exists_cover H d hd hH hn w P hPreal
      (ε := 1 / 4 ^ (k + 1)) (by positivity) (by
        rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num))
    refine ⟨N, hNP, ?_, fun p hp ↦ ?_⟩
    · simpa [one_div_one_div] using hNc
    · obtain ⟨q, hq, h⟩ := hNcov p hp
      exact ⟨q, hq, by rw [one_div_mul_eq_div] at h; exact h⟩
  have hch := chaining hd hn P a ha1 ha2 hcov (fun σ ↦ pat (φ σ))
    (fun σ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ σ))
  have hcorr : ∀ σ, corr σ (a (pat (φ σ))) =
      ∑ i, sgn (σ i) * (loss01 (φ σ) (W i).1 - loss01 (φ σ) (W i).2) := by
    intro σ
    unfold corr
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [a, pat, w, bitLoss, loss01, Fin.append_left, Fin.append_right]
  simp only [hcorr] at hch
  refine hch.trans ?_
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have e1 : sqrt (2 * m) ≤ 2 * sqrt (d * m) := by
    rw [mul_sqrt_eq 2 _ (by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have e2 : 5 * sqrt (40 * ((m + m : ℕ) : ℝ) * d) ≤ 45 * sqrt (d * m) := by
    rw [mul_sqrt_eq 5 _ (by norm_num), mul_sqrt_eq 45 _ (by norm_num)]
    apply Real.sqrt_le_sqrt
    push_cast
    nlinarith [mul_nonneg hm0 (by linarith : (0 : ℝ) ≤ d)]
  linarith

end UCOpt

-- ===== UCMcDiarmid =====

/-!
# McDiarmid's bounded-differences inequality (moment generating function form)

For a bounded measurable function `f` of `m` i.i.d. coordinates, changing any single coordinate
changes `f` by at most `c`, we show `E exp(λ (f − E f)) ≤ exp(λ² m c² / 2)`.
-/

open MeasureTheory Real

namespace UCOpt

variable {Z : Type*} [MeasurableSpace Z]

lemma integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs]; exact hC x)

lemma abs_exp_mul_sub_le (l a b B : ℝ) (ha : |a| ≤ B) :
    |exp (l * (a - b))| ≤ exp (|l| * (B + |b|)) := by
  rw [abs_of_pos (exp_pos _)]
  apply exp_le_exp.2
  calc l * (a - b) ≤ |l * (a - b)| := le_abs_self _
    _ = |l| * |a - b| := abs_mul _ _
    _ ≤ |l| * (B + |b|) := by
        gcongr
        exact (abs_sub _ _).trans (by linarith)

lemma abs_integral_le_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ} (C : ℝ) (hC : ∀ x, |g x| ≤ C) : |∫ x, g x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := C)
    (Filter.Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)
  simpa [Real.norm_eq_abs] using this

/-- **McDiarmid's inequality, mgf form.** -/
theorem mcdiarmid_mgf (D : Measure Z) [IsProbabilityMeasure D] :
    ∀ (m : ℕ) (f : (Fin m → Z) → ℝ), Measurable f → ∀ (B c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ B) →
      (∀ x x' : Fin m → Z, ∀ j, (∀ k, k ≠ j → x k = x' k) → |f x - f x'| ≤ c) → ∀ l : ℝ,
      ∫ x, exp (l * (f x - ∫ y, f y ∂(Measure.pi fun _ ↦ D))) ∂(Measure.pi fun _ ↦ D) ≤
        exp (l ^ 2 * m * c ^ 2 / 2) := by
  intro m
  induction m with
  | zero =>
    intro f _ B c _ _ _ l
    have hconst : ∀ x : Fin 0 → Z, f x = f default := fun x ↦ by rw [Subsingleton.elim x default]
    simp only [hconst, integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self,
      mul_zero, exp_zero, CharP.cast_eq_zero, zero_mul, zero_div, le_refl]
  | succ m ih =>
    intro f hf B c hc0 hB hc l
    set μ := Measure.pi fun _ : Fin m ↦ D
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ Z) 0
    have hmp : MeasurePreserving e.symm (D.prod μ) (Measure.pi fun _ ↦ D) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ D) 0).symm
    have he : ∀ y x, e.symm (y, x) = Fin.cons y x := by
      intro y x
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      try rfl
    set F : Z × (Fin m → Z) → ℝ := fun p ↦ f (e.symm p)
    have hFm : Measurable F := hf.comp e.symm.measurable
    have hFB : ∀ p, |F p| ≤ B := fun p ↦ hB _
    -- bounded differences of `F`
    have hFx : ∀ y, ∀ x x' : Fin m → Z, ∀ j, (∀ k, k ≠ j → x k = x' k) →
        |F (y, x) - F (y, x')| ≤ c := by
      intro y x x' j hj
      apply hc _ _ j.succ
      intro k hk
      simp only [he]
      refine Fin.cases ?_ (fun k' hk' ↦ ?_) k hk
      · intro _; rfl
      · simp only [Fin.cons_succ]
        exact hj k' (fun h ↦ hk' (by rw [h]))
    have hFy : ∀ y y' x, |F (y, x) - F (y', x)| ≤ c := by
      intro y y' x
      apply hc _ _ 0
      intro k hk
      simp only [he]
      obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.2 hk
      simp
    -- the partial average `h`
    set h : (Fin m → Z) → ℝ := fun x ↦ ∫ y, F (y, x) ∂D
    have hhm : Measurable h := (hFm.stronglyMeasurable.integral_prod_left' (μ := D)).measurable
    have hhB : ∀ x, |h x| ≤ B := fun x ↦ abs_integral_le_of_abs_le B fun y ↦ hFB _
    have hFint : ∀ x, Integrable (fun y ↦ F (y, x)) D := fun x ↦
      integrable_of_abs_le (hFm.comp (measurable_id.prodMk measurable_const)) B fun y ↦ hFB _
    have hhc : ∀ x x' : Fin m → Z, ∀ j, (∀ k, k ≠ j → x k = x' k) → |h x - h x'| ≤ c := by
      intro x x' j hj
      simp only [h]
      rw [← integral_sub (hFint x) (hFint x')]
      exact abs_integral_le_of_abs_le c fun y ↦ hFx y x x' j hj
    have hih := ih h hhm B c hc0 hhB hhc l
    set Eh := ∫ x, h x ∂μ
    have hFint2 : Integrable F (D.prod μ) := integrable_of_abs_le hFm B hFB
    have hEf : ∫ w, f w ∂(Measure.pi fun _ ↦ D) = Eh := by
      rw [← hmp.integral_comp' f]
      exact integral_prod_symm F hFint2
    rw [hEf, ← hmp.integral_comp' (fun w ↦ exp (l * (f w - Eh)))]
    have hGm : Measurable fun p : Z × (Fin m → Z) ↦ exp (l * (F p - Eh)) :=
      (measurable_const.mul (hFm.sub measurable_const)).exp
    have hGint : Integrable (fun p : Z × (Fin m → Z) ↦ exp (l * (F p - Eh))) (D.prod μ) :=
      integrable_of_abs_le hGm _ fun p ↦ abs_exp_mul_sub_le l _ _ B (hFB p)
    change ∫ p, exp (l * (F p - Eh)) ∂(D.prod μ) ≤ _
    rw [integral_prod_symm _ hGint]
    -- the inner integral, by Hoeffding's lemma
    have hinner : ∀ x, ∫ y, exp (l * (F (y, x) - Eh)) ∂D ≤
        exp (l * (h x - Eh)) * exp (c ^ 2 * l ^ 2 / 2) := by
      intro x
      have hsplit : ∀ y, exp (l * (F (y, x) - Eh)) =
          exp (l * (h x - Eh)) * exp (l * (F (y, x) - h x)) := by
        intro y; rw [← exp_add]; ring_nf
      simp only [hsplit]
      rw [integral_const_mul]
      gcongr
      rcases isEmpty_or_nonempty Z with hZ | ⟨⟨y0⟩⟩
      · have : D = 0 := Measure.eq_zero_of_isEmpty D
        exact absurd this (IsProbabilityMeasure.ne_zero D)
      have hX : ProbabilityTheory.HasSubgaussianMGF (fun y ↦ F (y, x) - h x)
          ((‖(F (y0, x) + c - h x) - (F (y0, x) - c - h x)‖₊ / 2) ^ 2) D := by
        apply ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        · exact ((hFm.comp (measurable_id.prodMk measurable_const)).sub
            measurable_const).aemeasurable
        · refine Filter.Eventually.of_forall fun y ↦ ?_
          have := hFy y y0 x
          rw [abs_le] at this
          constructor <;> linarith [this.1, this.2]
        · rw [integral_sub (hFint x) (integrable_const _)]
          simp [h]
      have := hX.mgf_le l
      unfold ProbabilityTheory.mgf at this
      refine this.trans (le_of_eq ?_)
      congr 1
      have : (F (y0, x) + c - h x) - (F (y0, x) - c - h x) = 2 * c := by ring
      rw [this]
      push_cast
      simp only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 2 * c by linarith)]
      ring
    have hhint : Integrable (fun x ↦ exp (l * (h x - Eh))) μ :=
      integrable_of_abs_le (measurable_const.mul (hhm.sub measurable_const)).exp _
        fun x ↦ abs_exp_mul_sub_le l _ _ B (hhB x)
    calc ∫ x, ∫ y, exp (l * (F (y, x) - Eh)) ∂D ∂μ
        ≤ ∫ x, exp (l * (h x - Eh)) * exp (c ^ 2 * l ^ 2 / 2) ∂μ := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun x ↦
              integral_nonneg fun y ↦ (exp_pos _).le
          · exact hhint.mul_const _
          · exact Filter.Eventually.of_forall hinner
      _ = (∫ x, exp (l * (h x - Eh)) ∂μ) * exp (c ^ 2 * l ^ 2 / 2) := integral_mul_const _ _
      _ ≤ exp (l ^ 2 * m * c ^ 2 / 2) * exp (c ^ 2 * l ^ 2 / 2) := by gcongr
      _ = exp (l ^ 2 * ((m + 1 : ℕ) : ℝ) * c ^ 2 / 2) := by
          rw [← exp_add]; push_cast; ring_nf

/-- **McDiarmid's inequality.** Tail bound for bounded-difference functions of i.i.d. samples. -/
theorem mcdiarmid (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 1 ≤ m)
    (f : (Fin m → Z) → ℝ) (hf : Measurable f) (B c : ℝ) (hc0 : 0 < c) (hB : ∀ x, |f x| ≤ B)
    (hc : ∀ x x' : Fin m → Z, ∀ j, (∀ k, k ≠ j → x k = x' k) → |f x - f x'| ≤ c)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi fun _ ↦ D).real {x | (∫ y, f y ∂(Measure.pi fun _ ↦ D)) + t ≤ f x} ≤
      exp (-(t ^ 2 / (2 * m * c ^ 2))) := by
  set μ := Measure.pi fun _ : Fin m ↦ D
  set E := ∫ y, f y ∂μ
  set l := t / (m * c ^ 2)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hl : 0 ≤ l := by positivity
  have hset : {x | E + t ≤ f x} = {x | t ≤ f x - E} := by ext x; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  rw [hset]
  have hint : Integrable (fun x ↦ exp (l * (f x - E))) μ :=
    integrable_of_abs_le (measurable_const.mul (hf.sub measurable_const)).exp _
      fun x ↦ abs_exp_mul_sub_le l _ _ B (hB x)
  refine (ProbabilityTheory.measure_ge_le_exp_mul_mgf (X := fun x ↦ f x - E) t hl hint).trans ?_
  unfold ProbabilityTheory.mgf
  have hmgf := mcdiarmid_mgf D m f hf B c hc0.le hB hc l
  calc exp (-l * t) * ∫ x, exp (l * (f x - E)) ∂μ ≤ exp (-l * t) * exp (l ^ 2 * m * c ^ 2 / 2) := by
        gcongr
    _ = exp (-(t ^ 2 / (2 * m * c ^ 2))) := by
        rw [← exp_add]; congr 1; simp only [l]; field_simp; ring

end UCOpt

-- ===== UCSymmetrization =====

/-!
# Symmetrization

For a countable family of `[0, 1]`-valued measurable functions,
`E_S sup_n |L_S(g_n) − L_D(g_n)|` is bounded by any uniform bound on the Rademacher averages
`E_σ sup_n |(1/m) ∑ᵢ σᵢ (g_n(zᵢ) − g_n(z'ᵢ))|` over double samples.
-/

open MeasureTheory Real

namespace UCOpt

variable {Z : Type*} [MeasurableSpace Z]

lemma le_iSup_of_abs_le (x : ℕ → ℝ) (C : ℝ) (h : ∀ n, |x n| ≤ C) (n : ℕ) :
    |x n| ≤ ⨆ k, |x k| :=
  le_ciSup (f := fun k ↦ |x k|) ⟨C, by rintro _ ⟨k, rfl⟩; exact h k⟩ n

lemma iSup_abs_le (x : ℕ → ℝ) (C : ℝ) (h : ∀ n, |x n| ≤ C) : ⨆ k, |x k| ≤ C :=
  ciSup_le h

lemma iSup_abs_nonneg (x : ℕ → ℝ) (C : ℝ) (h : ∀ n, |x n| ≤ C) : 0 ≤ ⨆ k, |x k| :=
  (abs_nonneg (x 0)).trans (le_iSup_of_abs_le x C h 0)

omit [MeasurableSpace Z] in
lemma eavg_mem {m : ℕ} (hm : 1 ≤ m) (g : Z → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    (S : Fin m → Z) : 0 ≤ (∑ i, g (S i)) / m ∧ (∑ i, g (S i)) / m ≤ 1 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ ↦ hg0 _) hmpos.le
  · rw [div_le_one hmpos]
    calc ∑ i, g (S i) ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ ↦ hg1 _
      _ = m := by simp

lemma integral_mem (D : Measure Z) [IsProbabilityMeasure D] (g : Z → ℝ) (hg0 : ∀ z, 0 ≤ g z)
    (hg1 : ∀ z, g z ≤ 1) : 0 ≤ ∫ z, g z ∂D ∧ ∫ z, g z ∂D ≤ 1 := by
  constructor
  · exact integral_nonneg hg0
  · have := norm_integral_le_of_norm_le_const (μ := D) (f := g) (C := 1)
      (Filter.Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 z)]; exact hg1 z)
    simp only [Real.norm_eq_abs, probReal_univ, mul_one] at this
    exact (le_abs_self _).trans this

lemma abs_sub_le_one_of_mem {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    |a - b| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma integral_eavg (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 1 ≤ m) (g : Z → ℝ)
    (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1) :
    ∫ S, (∑ i, g (S i)) / m ∂(Measure.pi fun _ : Fin m ↦ D) = ∫ z, g z ∂D := by
  have hint : ∀ i : Fin m, Integrable (fun S : Fin m → Z ↦ g (S i))
      (Measure.pi fun _ : Fin m ↦ D) := by
    intro i
    refine Integrable.of_bound (hg.comp (measurable_pi_apply i)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun S ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]; exact hg1 _
  rw [integral_div, integral_finset_sum _ fun i _ ↦ hint i]
  have heach : ∀ i : Fin m, ∫ S, g (S i) ∂(Measure.pi fun _ : Fin m ↦ D) = ∫ z, g z ∂D := by
    intro i
    have hmp := measurePreserving_eval (fun _ : Fin m ↦ D) i
    have := integral_map (μ := Measure.pi fun _ : Fin m ↦ D) hmp.measurable.aemeasurable
      (hg.aestronglyMeasurable (μ := Measure.map (Function.eval i) (Measure.pi fun _ ↦ D)))
    rw [hmp.map_eq] at this
    exact this.symm
  simp only [heach, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  field_simp

/-- **Symmetrization.** -/
theorem symmetrization (D : Measure Z) [IsProbabilityMeasure D] (m : ℕ) (hm : 1 ≤ m)
    (g : ℕ → Z → ℝ) (hg : ∀ n, Measurable (g n)) (hg0 : ∀ n z, 0 ≤ g n z)
    (hg1 : ∀ n z, g n z ≤ 1) (R : ℝ) (hR : ∀ W : Fin m → Z × Z,
      savg m (fun σ ↦ ⨆ n, |(∑ i, sgn (σ i) * (g n (W i).1 - g n (W i).2)) / m|) ≤ R) :
    ∫ S, (⨆ n, |(∑ i, g n (S i)) / m - ∫ z, g n z ∂D|) ∂(Measure.pi fun _ : Fin m ↦ D) ≤ R := by
  set μ := Measure.pi fun _ : Fin m ↦ D
  set ν := Measure.pi fun _ : Fin m ↦ D.prod D
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set ea : ℕ → (Fin m → Z) → ℝ := fun n S ↦ (∑ i, g n (S i)) / m
  have hea : ∀ n S, 0 ≤ ea n S ∧ ea n S ≤ 1 := fun n S ↦ eavg_mem hm (g n) (hg0 n) (hg1 n) S
  have heam : ∀ n, Measurable (ea n) := fun n ↦
    (Finset.measurable_sum _ fun i _ ↦ (hg n).comp (measurable_pi_apply i)).div_const _
  set Φ : (Fin m → Z) → ℝ := fun S ↦ ⨆ n, |ea n S - ∫ z, g n z ∂D|
  set Ψ : (Fin m → Z) × (Fin m → Z) → ℝ := fun p ↦ ⨆ n, |ea n p.1 - ea n p.2|
  have hΦb : ∀ S n, |ea n S - ∫ z, g n z ∂D| ≤ 1 := fun S n ↦
    abs_sub_le_one_of_mem (hea n S) (integral_mem D (g n) (hg0 n) (hg1 n))
  have hΨb : ∀ p : (Fin m → Z) × (Fin m → Z), ∀ n, |ea n p.1 - ea n p.2| ≤ 1 := fun p n ↦
    abs_sub_le_one_of_mem (hea n p.1) (hea n p.2)
  have hΦm : Measurable Φ := Measurable.iSup fun n ↦ ((heam n).sub measurable_const).abs
  have hΨm : Measurable Ψ := Measurable.iSup fun n ↦
    (((heam n).comp measurable_fst).sub ((heam n).comp measurable_snd)).abs
  have hΨabs : ∀ p, |Ψ p| ≤ 1 := fun p ↦ by
    rw [abs_of_nonneg (iSup_abs_nonneg _ 1 (hΨb p))]; exact iSup_abs_le _ 1 (hΨb p)
  have hΨint : Integrable Ψ (μ.prod μ) :=
    Integrable.of_bound hΨm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun p ↦ by
      rw [Real.norm_eq_abs]; exact hΨabs p)
  -- step 1: `Φ S ≤ E_{S'} Ψ (S, S')`
  have hstep1 : ∀ S, Φ S ≤ ∫ S', Ψ (S, S') ∂μ := by
    intro S
    have hΨSint : Integrable (fun S' ↦ Ψ (S, S')) μ :=
      Integrable.of_bound (hΨm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        1 (Filter.Eventually.of_forall fun S' ↦ by rw [Real.norm_eq_abs]; exact hΨabs _)
    refine ciSup_le fun n ↦ ?_
    have hint_ea : Integrable (ea n) μ := Integrable.of_bound (heam n).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun S' ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hea n S').1]; exact (hea n S').2)
    have e1 : ea n S - ∫ z, g n z ∂D = ∫ S', (ea n S - ea n S') ∂μ := by
      rw [integral_sub (integrable_const _) hint_ea, integral_const, probReal_univ, one_smul]
      simp only [ea]
      rw [integral_eavg D m hm (g n) (hg n) (hg0 n) (hg1 n)]
    rw [e1]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono ((integrable_const _).sub hint_ea).abs hΨSint fun S' ↦ ?_
    exact le_iSup_of_abs_le (fun k ↦ ea k S - ea k S') 1 (fun k ↦ hΨb (S, S') k) n
  -- step 2: integrate and use Fubini
  have hΦint : Integrable Φ μ := Integrable.of_bound hΦm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun S ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (iSup_abs_nonneg _ 1 (hΦb S))]
      exact iSup_abs_le _ 1 (hΦb S))
  have hstep2 : ∫ S, Φ S ∂μ ≤ ∫ p, Ψ p ∂(μ.prod μ) := by
    rw [integral_prod Ψ hΨint]
    exact integral_mono hΦint hΨint.integral_prod_left hstep1
  -- step 3: pass to the product of pairs
  have hmpE := measurePreserving_arrowProdEquivProdArrow Z Z (Fin m) (fun _ ↦ D) (fun _ ↦ D)
  set Ψ' : (Fin m → Z × Z) → ℝ := fun W ↦ ⨆ n, |(∑ i, (g n (W i).1 - g n (W i).2)) / m|
  have hstep3 : ∫ p, Ψ p ∂(μ.prod μ) = ∫ W, Ψ' W ∂ν := by
    rw [← hmpE.integral_comp' Ψ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun W ↦ ?_)
    simp only [Ψ, Ψ', ea]
    congr 1; funext n
    rw [← sub_div, ← Finset.sum_sub_distrib]
    rfl
  -- step 4: random swaps
  set sw : (Fin m → Bool) → (Fin m → Z × Z) → (Fin m → Z × Z) :=
    fun σ W i ↦ if σ i then W i else (W i).swap
  have hswmp : ∀ σ, MeasurePreserving (sw σ) ν ν := by
    intro σ
    apply measurePreserving_pi (fun _ ↦ D.prod D) (fun _ ↦ D.prod D)
      (f := fun i (z : Z × Z) ↦ if σ i then z else z.swap)
    intro i
    by_cases h : σ i
    · simp only [h, if_true]; exact MeasurePreserving.id _
    · simp only [h, Bool.false_eq_true, if_false]; exact Measure.measurePreserving_swap
  set Ψσ : (Fin m → Bool) → (Fin m → Z × Z) → ℝ := fun σ W ↦
    ⨆ n, |(∑ i, sgn (σ i) * (g n (W i).1 - g n (W i).2)) / m|
  have hΨ'sw : ∀ σ W, Ψ' (sw σ W) = Ψσ σ W := by
    intro σ W
    simp only [Ψ', Ψσ, sw]
    congr 1; funext n; congr 2
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    cases σ i <;> simp [sgn]
  have hΨ'm : Measurable Ψ' := Measurable.iSup fun n ↦
    ((Finset.measurable_sum _ fun i _ ↦ ((hg n).comp (measurable_fst.comp
      (measurable_pi_apply i))).sub ((hg n).comp (measurable_snd.comp
      (measurable_pi_apply i)))).div_const _).abs
  have hswint : ∀ σ, ∫ W, Ψ' W ∂ν = ∫ W, Ψσ σ W ∂ν := by
    intro σ
    have := integral_map (μ := ν) (hswmp σ).measurable.aemeasurable
      (hΨ'm.aestronglyMeasurable (μ := Measure.map (sw σ) ν))
    rw [(hswmp σ).map_eq] at this
    rw [this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun W ↦ hΨ'sw σ W)
  have hΨσb : ∀ (σ : Fin m → Bool) (W : Fin m → Z × Z) (n : ℕ), |(∑ i, sgn (σ i) * (g n (W i).1 - g n (W i).2)) / m| ≤ 1 := by
    intro σ W n
    rw [abs_div, abs_of_pos hmpos, div_le_one hmpos]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |sgn (σ i) * (g n (W i).1 - g n (W i).2)| ≤ ∑ _i : Fin m, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul]
          have hs : |sgn (σ i)| = 1 := by cases σ i <;> simp [sgn]
          rw [hs, one_mul]
          exact abs_sub_le_one_of_mem ⟨hg0 _ _, hg1 _ _⟩ ⟨hg0 _ _, hg1 _ _⟩
      _ = m := by simp
  have hΨσint : ∀ σ, Integrable (Ψσ σ) ν := by
    intro σ
    have hm' : Measurable (Ψσ σ) := by
      have : Ψσ σ = Ψ' ∘ sw σ := funext fun W ↦ (hΨ'sw σ W).symm
      rw [this]; exact hΨ'm.comp (hswmp σ).measurable
    refine Integrable.of_bound hm'.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun W ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (iSup_abs_nonneg _ 1 (hΨσb σ W))]
    exact iSup_abs_le _ 1 (hΨσb σ W)
  have hstep4 : ∫ W, Ψ' W ∂ν = ∫ W, savg m (fun σ ↦ Ψσ σ W) ∂ν := by
    unfold savg
    rw [integral_div, integral_finset_sum _ fun σ _ ↦ hΨσint σ]
    simp only [← hswint, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  calc ∫ S, Φ S ∂μ ≤ ∫ p, Ψ p ∂(μ.prod μ) := hstep2
    _ = ∫ W, savg m (fun σ ↦ Ψσ σ W) ∂ν := by rw [hstep3, hstep4]
    _ ≤ ∫ _W, R ∂ν := by
        refine integral_mono ?_ (integrable_const _) fun W ↦ hR W
        unfold savg
        exact (integrable_finset_sum _ fun σ _ ↦ hΨσint σ).div_const _
    _ = R := by simp

end UCOpt

-- ===== UCBinary =====

/-!
# Theorem 6.8, part 1: uniform convergence for VC classes at the optimal rate

`m^{UC}(ε, δ) ≤ ⌈C (d + log(1/δ))/ε²⌉` with `C = 8836`, via symmetrization, chaining
(with a Haussler-type packing bound) and McDiarmid's inequality.
-/

open MeasureTheory Real UnderstandingML

namespace UCOpt

variable {X : Type*} [MeasurableSpace X]

lemma measurable_loss01 {h : X → Bool} (hh : Measurable h) :
    Measurable (fun z : X × Bool ↦ loss01 h z) := by
  have hs : MeasurableSet {p : X × Bool | h p.1 = p.2} := by
    have : {p : X × Bool | h p.1 = p.2} = ⋃ b : Bool, (h ⁻¹' {b}) ×ˢ {b} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_preimage,
        Set.mem_singleton_iff]
      exact ⟨fun h' ↦ ⟨p.2, h', rfl⟩, fun ⟨b, h1, h2⟩ ↦ h1.trans h2.symm⟩
    rw [this]
    exact MeasurableSet.iUnion fun b ↦ (hh (measurableSet_singleton b)).prod
      (measurableSet_singleton b)
  unfold loss01
  exact Measurable.ite hs measurable_const measurable_const

omit [MeasurableSpace X] in
lemma loss01_nonneg (h : X → Bool) (z : X × Bool) : 0 ≤ loss01 h z := by
  unfold loss01; split_ifs <;> norm_num

omit [MeasurableSpace X] in
lemma loss01_le_one (h : X → Bool) (z : X × Bool) : loss01 h z ≤ 1 := by
  unfold loss01; split_ifs <;> norm_num

/-- Countable approximation: a large deviation for some `h ∈ H` is witnessed by a member of the
countable subclass. -/
lemma exists_enum_deviation (H : Set (X → Bool)) (hmeas : ∀ h ∈ H, Measurable h)
    (e : ℕ → X → Bool) (happrox : ∀ h ∈ H, ∃ u : ℕ → (X → Bool), (∀ n, u n ∈ Set.range e) ∧
      ∀ x, ∃ N, ∀ n, N ≤ n → u n x = h x) (heH : ∀ n, e n ∈ H)
    (D : Measure (X × Bool)) [IsProbabilityMeasure D] {m : ℕ} (S : Fin m → X × Bool)
    {ε : ℝ} (h : X → Bool) (hH : h ∈ H)
    (hbad : ε < |empRisk loss01 S h - risk loss01 D h|) :
    ∃ n, ε < |empRisk loss01 S (e n) - risk loss01 D (e n)| := by
  obtain ⟨u, hu, hconv⟩ := happrox h hH
  have hev : ∀ x, ∀ᶠ k in Filter.atTop, u k x = h x := fun x ↦ by
    obtain ⟨N, hN⟩ := hconv x
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  have hemp : Filter.Tendsto (fun k ↦ empRisk loss01 S (u k)) Filter.atTop
      (nhds (empRisk loss01 S h)) := by
    have hall : ∀ᶠ k in Filter.atTop, ∀ i, u k (S i).1 = h (S i).1 :=
      Filter.eventually_all.2 fun i ↦ hev (S i).1
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hall] with k hk
    unfold empRisk loss01
    simp only [hk]
  have humeas : ∀ k, Measurable (u k) := fun k ↦ by
    obtain ⟨n, hn⟩ := hu k; rw [← hn]; exact hmeas _ (heH n)
  have hrisk : Filter.Tendsto (fun k ↦ risk loss01 D (u k)) Filter.atTop
      (nhds (risk loss01 D h)) := by
    unfold risk
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (fun k ↦ (measurable_loss01 (humeas k)).aestronglyMeasurable) (integrable_const _)
      (fun k ↦ Filter.Eventually.of_forall fun z ↦ ?_) (Filter.Eventually.of_forall fun z ↦ ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (loss01_nonneg _ _)]; exact loss01_le_one _ _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev z.1] with k hk
      unfold loss01; rw [hk]
  have hlim := ((hemp.sub hrisk).abs).eventually (lt_mem_nhds hbad)
  obtain ⟨k, hk⟩ := hlim.exists
  obtain ⟨n, hn⟩ := hu k
  exact ⟨n, by rw [hn]; exact hk⟩

/-- The sup over a sequence whose values factor through a finite type is attained. -/
lemma exists_max_of_factor {ι : Type*} [Finite ι] (q : ℕ → ι) (F : ι → ℝ) :
    ∃ n0, ∀ n, F (q n) ≤ F (q n0) := by
  have hfin : (Set.range q).Finite := (Set.range q).toFinite
  obtain ⟨p, ⟨n0, rfl⟩, hp⟩ := Set.exists_max_image (Set.range q) F hfin ⟨q 0, 0, rfl⟩
  exact ⟨n0, fun n ↦ hp (q n) ⟨n, rfl⟩⟩

lemma iSup_eq_of_max (x : ℕ → ℝ) (n0 : ℕ) (h : ∀ n, x n ≤ x n0) : ⨆ n, x n = x n0 :=
  le_antisymm (ciSup_le h) (le_ciSup ⟨x n0, by rintro _ ⟨n, rfl⟩; exact h n⟩ n0)

end UCOpt

open UCOpt

/-- **Theorem 6.8, part 1** (uniform convergence at the optimal rate). -/
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ),
        (∀ h ∈ H, Measurable h) → PointwiseSeparable H → vcDim H ≤ d → 1 ≤ d →
        HasUniformConvergenceWith loss01 H
          (fun ε δ ↦ ⌈C * (d + Real.log (1 / δ)) / ε ^ 2⌉₊) := by
  refine ⟨8836, by norm_num, ?_⟩
  intro X _ H d hmeas hsep hvc hd1 ε δ hε hε1 hδ hδ1 D hD m hm
  classical
  set L := Real.log (1 / δ)
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hmreal : 8836 * (d + L) / ε ^ 2 ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have hm1 : 1 ≤ m := by
    have : 0 < 8836 * (d + L) / ε ^ 2 := by positivity
    have : (0 : ℝ) < m := lt_of_lt_of_le this hmreal
    exact_mod_cast this
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmε : 8836 * (d + L) ≤ ε ^ 2 * m := by
    rw [div_le_iff₀ (by positivity)] at hmreal; linarith
  -- trivial case: empty class
  rcases H.eq_empty_or_nonempty with hHe | ⟨h₀, hh₀⟩
  · have : {S : Fin m → X × Bool | ¬ IsRepresentative loss01 H D ε S} = ∅ := by
      ext S; simp [IsRepresentative, hHe]
    rw [this, measure_empty]; simp
  obtain ⟨H₀, hH₀H, hH₀c, happrox⟩ := hsep
  have hH₀ne : H₀.Nonempty := by
    obtain ⟨u, hu, -⟩ := happrox h₀ hh₀
    exact ⟨u 0, hu 0⟩
  obtain ⟨e, he⟩ := hH₀c.exists_eq_range hH₀ne
  have heH : ∀ n, e n ∈ H := fun n ↦ hH₀H (by rw [he]; exact ⟨n, rfl⟩)
  have happrox' : ∀ h ∈ H, ∃ u : ℕ → (X → Bool), (∀ n, u n ∈ Set.range e) ∧
      ∀ x, ∃ N, ∀ n, N ≤ n → u n x = h x := by
    intro h hh
    obtain ⟨u, hu, hc⟩ := happrox h hh
    exact ⟨u, fun n ↦ by rw [← he]; exact hu n, hc⟩
  set g : ℕ → X × Bool → ℝ := fun n z ↦ loss01 (e n) z
  have hgm : ∀ n, Measurable (g n) := fun n ↦ measurable_loss01 (hmeas _ (heH n))
  have hg0 : ∀ n z, 0 ≤ g n z := fun n z ↦ loss01_nonneg _ _
  have hg1 : ∀ n z, g n z ≤ 1 := fun n z ↦ loss01_le_one _ _
  set μ := Measure.pi fun _ : Fin m ↦ D
  set Φ : (Fin m → X × Bool) → ℝ := fun S ↦ ⨆ n, |(∑ i, g n (S i)) / m - ∫ z, g n z ∂D|
  have hΦb : ∀ (S : Fin m → X × Bool) (n : ℕ), |(∑ i, g n (S i)) / m - ∫ z, g n z ∂D| ≤ 1 := fun S n ↦
    abs_sub_le_one_of_mem (eavg_mem hm1 (g n) (hg0 n) (hg1 n) S)
      (integral_mem D (g n) (hg0 n) (hg1 n))
  have hΦabs : ∀ S, |Φ S| ≤ 1 := fun S ↦ by
    rw [abs_of_nonneg (iSup_abs_nonneg _ 1 (hΦb S))]; exact iSup_abs_le _ 1 (hΦb S)
  have hΦm : Measurable Φ := Measurable.iSup fun n ↦
    (((Finset.measurable_sum _ fun i _ ↦ (hgm n).comp (measurable_pi_apply i)).div_const _).sub
      measurable_const).abs
  -- the expected supremum is small
  have hexp : ∫ S, Φ S ∂μ ≤ 47 * Real.sqrt (d * m) / m := by
    apply symmetrization D m hm1 g hgm hg0 hg1
    intro W
    -- for each sign vector, the supremum is attained at some `e (n₀ σ)`
    have hmax : ∀ σ : Fin m → Bool, ∃ n0, ∀ n,
        |(∑ i, sgn (σ i) * (g n (W i).1 - g n (W i).2)) / m| ≤
          |(∑ i, sgn (σ i) * (g n0 (W i).1 - g n0 (W i).2)) / m| := by
      intro σ
      obtain ⟨n0, hn0⟩ := exists_max_of_factor
        (fun n (i : Fin m) ↦ (e n (W i).1.1, e n (W i).2.1))
        (fun p ↦ |(∑ i, sgn (σ i) * (bitLoss (p i).1 (W i).1.2 - bitLoss (p i).2 (W i).2.2)) / m|)
      refine ⟨n0, fun n ↦ ?_⟩
      have := hn0 n
      simpa [g, loss01, bitLoss] using this
    choose n0 hn0 using hmax
    have hsup : ∀ σ, (⨆ n, |(∑ i, sgn (σ i) * (g n (W i).1 - g n (W i).2)) / m|) =
        |∑ i, sgn (σ i) * (loss01 (e (n0 σ)) (W i).1 - loss01 (e (n0 σ)) (W i).2)| / m := by
      intro σ
      rw [iSup_eq_of_max _ (n0 σ) (hn0 σ), abs_div, abs_of_pos hmpos]
    simp only [hsup]
    have hrad := rademacher_vc H d hd1 hvc hm1 W (fun σ ↦ e (n0 σ)) (fun σ ↦ heH _)
    unfold savg at hrad ⊢
    rw [← Finset.sum_div, div_right_comm]
    exact div_le_div_of_nonneg_right hrad hmpos.le
  have hexp2 : ∫ S, Φ S ∂μ ≤ ε / 2 := by
    refine hexp.trans ?_
    rw [div_le_iff₀ hmpos]
    have hsq : 47 * Real.sqrt (d * m) ≤ ε / 2 * m := by
      rw [show ε / 2 * m = Real.sqrt ((ε / 2 * m) ^ 2) by
        rw [Real.sqrt_sq (by positivity)], mul_sqrt_eq 47 _ (by norm_num)]
      apply Real.sqrt_le_sqrt
      have : 8836 * d ≤ ε ^ 2 * m := by nlinarith
      nlinarith
    exact hsq
  -- bad samples have a large supremum
  have hsub : {S : Fin m → X × Bool | ¬ IsRepresentative loss01 H D ε S} ⊆
      {S | (∫ S, Φ S ∂μ) + ε / 2 ≤ Φ S} := by
    intro S hS
    simp only [IsRepresentative, not_forall, not_le, exists_prop, Set.mem_setOf_eq] at hS
    obtain ⟨h, hH, hbad⟩ := hS
    obtain ⟨n, hn⟩ := exists_enum_deviation H hmeas e happrox' heH D S h hH hbad
    have : ε < Φ S := lt_of_lt_of_le hn (le_iSup_of_abs_le _ 1 (hΦb S) n)
    simp only [Set.mem_setOf_eq]
    linarith
  -- bounded differences
  have hbd : ∀ S S' : Fin m → X × Bool, ∀ j, (∀ k, k ≠ j → S k = S' k) →
      |Φ S - Φ S'| ≤ 1 / m := by
    have key : ∀ S S' : Fin m → X × Bool, ∀ j, (∀ k, k ≠ j → S k = S' k) →
        Φ S ≤ Φ S' + 1 / m := by
      intro S S' j hj
      refine ciSup_le fun n ↦ ?_
      have hdiff : |(∑ i, g n (S i)) / m - (∑ i, g n (S' i)) / m| ≤ 1 / m := by
        rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hmpos]
        rw [Finset.sum_eq_single j (fun k _ hk ↦ by rw [hj k hk, sub_self])
          (fun h ↦ absurd (Finset.mem_univ j) h)]
        gcongr
        exact abs_sub_le_one_of_mem ⟨hg0 _ _, hg1 _ _⟩ ⟨hg0 _ _, hg1 _ _⟩
      have h1 := le_iSup_of_abs_le _ 1 (hΦb S') n
      have h2 := abs_sub_abs_le_abs_sub ((∑ i, g n (S i)) / m - ∫ z, g n z ∂D)
        ((∑ i, g n (S' i)) / m - ∫ z, g n z ∂D)
      have h3 : (∑ i, g n (S i)) / m - ∫ z, g n z ∂D -
          ((∑ i, g n (S' i)) / m - ∫ z, g n z ∂D) =
          (∑ i, g n (S i)) / m - (∑ i, g n (S' i)) / m := by ring
      rw [h3] at h2
      linarith
    intro S S' j hj
    rw [abs_le]
    constructor
    · have := key S' S j (fun k hk ↦ (hj k hk).symm); linarith
    · have := key S S' j hj; linarith
  -- McDiarmid
  have hmc := mcdiarmid D m hm1 Φ hΦm 1 (1 / m) (by positivity) hΦabs hbd (ε / 2) (by positivity)
  have hexpδ : Real.exp (-((ε / 2) ^ 2 / (2 * m * (1 / m) ^ 2))) ≤ δ := by
    have e1 : (ε / 2) ^ 2 / (2 * m * (1 / m) ^ 2) = ε ^ 2 * m / 8 := by
      field_simp; ring
    rw [e1]
    have : L ≤ ε ^ 2 * m / 8 := by nlinarith
    calc Real.exp (-(ε ^ 2 * m / 8)) ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)
      _ = δ := by
        simp only [L]
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
  calc iidLaw D m {S | ¬ IsRepresentative loss01 H D ε S}
      ≤ μ {S | (∫ S, Φ S ∂μ) + ε / 2 ≤ Φ S} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {S | (∫ S, Φ S ∂μ) + ε / 2 ≤ Φ S}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (hmc.trans hexpδ)
