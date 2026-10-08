-- Prove2me | solution 1 for TalagrandConc.SymmetricGroup.cor_5_9
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:14:13.779572+00:00
-- url     : https://prove2.me/submissions/e4d9ab2a-4d1c-44e4-8a42-f1400ce2c851

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic



namespace TalagrandConc.SymmetricGroup

open scoped ENNReal Classical
open Equiv

/-! ### Basic geometry of `U`, `V` -/

lemma U_finite {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) : (U A σ).Finite := by
  apply (Set.finite_range (fun b : Fin N → Bool => fun i => if b i then (1 : ℝ) else 0)).subset
  intro s hs
  refine ⟨fun i => decide (s i = 1), ?_⟩
  funext i
  rcases hs.1 i with h | h <;> simp [h]

lemma V_compact {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) : IsCompact (V A σ) :=
  (U_finite A σ).isCompact_convexHull ℝ

lemma V_convex {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) : Convex ℝ (V A σ) :=
  convex_convexHull ℝ _

lemma U_subset_box {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) :
    U A σ ⊆ Set.Icc (0 : Fin N → ℝ) 1 := by
  intro s hs
  refine ⟨fun ℓ => ?_, fun ℓ => ?_⟩ <;> rcases hs.1 ℓ with h | h <;> simp [h]

lemma V_subset_box {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) :
    V A σ ⊆ Set.Icc (0 : Fin N → ℝ) 1 :=
  convexHull_min (U_subset_box A σ) (convex_Icc _ _)

lemma V_coord {N : ℕ} {A : Set (Perm (Fin N))} {σ : Perm (Fin N)} {s : Fin N → ℝ}
    (hs : s ∈ V A σ) (ℓ : Fin N) : 0 ≤ s ℓ ∧ s ℓ ≤ 1 :=
  ⟨(V_subset_box A σ hs).1 ℓ, (V_subset_box A σ hs).2 ℓ⟩

/-- Infimum of `ofReal ∘ F` over a compact set: `⊤` if empty, attained otherwise. -/
lemma iInf_ofReal_cases {N : ℕ} (S : Set (Fin N → ℝ)) (hS : IsCompact S)
    (F : (Fin N → ℝ) → ℝ) (hF : Continuous F) :
    (S = ∅ ∧ (⨅ x ∈ S, ENNReal.ofReal (F x)) = ⊤) ∨
      (∃ s ∈ S, (⨅ x ∈ S, ENNReal.ofReal (F x)) = ENNReal.ofReal (F s) ∧ ∀ x ∈ S, F s ≤ F x) := by
  rcases S.eq_empty_or_nonempty with h | h
  · left; refine ⟨h, ?_⟩; simp [h]
  · right
    obtain ⟨s, hs, hmin⟩ := hS.exists_isMinOn h hF.continuousOn
    refine ⟨s, hs, le_antisymm (iInf₂_le s hs) ?_, fun x hx => hmin hx⟩
    exact le_iInf₂ fun x hx => ENNReal.ofReal_le_ofReal (hmin hx)

lemma sum_split {N : ℕ} (i j : Fin N) (hij : i ≠ j) (h : Fin N → ℝ) :
    ∑ ℓ, h ℓ = h i + h j + ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), h ℓ := by
  have e : Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j) = (Finset.univ.erase i).erase j := by
    ext ℓ; simp [and_comm]
  rw [e, ← Finset.add_sum_erase _ h (Finset.mem_univ i),
    ← Finset.add_sum_erase _ h (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩), add_assoc]

lemma cont_fp {N : ℕ} (i : Fin N) :
    Continuous (fun s : Fin N → ℝ => s i ^ 2 + ∑ ℓ, s ℓ ^ 2) :=
  ((continuous_apply i).pow 2).add (continuous_finsetSum _ fun ℓ _ => (continuous_apply ℓ).pow 2)

lemma cont_g {N : ℕ} (i j : Fin N) :
    Continuous (fun s : Fin N → ℝ =>
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), s ℓ ^ 2) :=
  continuous_finsetSum _ fun ℓ _ => (continuous_apply ℓ).pow 2

lemma T_compact {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (m : Fin N) :
    IsCompact {s ∈ V A σ | s m = 0} :=
  (V_compact A σ).inter_right (isClosed_eq (continuous_apply m) continuous_const)

/-- Pointwise convexity bound used for every coordinate. -/
lemma coord_bound (a c u v : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1) :
    (a * u + c * v) ^ 2 ≤ a * u ^ 2 + c * v ^ 2 := by
  have : a * u ^ 2 + c * v ^ 2 - (a * u + c * v) ^ 2 = a * c * (u - v) ^ 2 := by
    have hc' : c = 1 - a := by linarith
    subst hc'; ring
  nlinarith [mul_nonneg (mul_nonneg ha hc) (sq_nonneg (u - v))]

lemma coord_bound_j (a c u v : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hu : 0 ≤ u) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (a * u + c * v) ^ 2 ≤ 2 * a * u ^ 2 + 2 * c ^ 2 := by
  have h1 : (a * u + c * v) ^ 2 ≤ (a * u + c) ^ 2 := by
    have : a * u + c * v ≤ a * u + c := by nlinarith
    have h0 : 0 ≤ a * u + c * v := by positivity
    nlinarith
  have h2 : 2 * (a * c) * u ≤ a * u ^ 2 + a * c ^ 2 := by
    nlinarith [mul_nonneg ha (sq_nonneg (u - c))]
  have h3 : a ^ 2 ≤ a := by nlinarith
  have h4 : a * c ^ 2 ≤ c ^ 2 := by nlinarith [sq_nonneg c]
  nlinarith

/-- The real inequality behind Lemma 5.3. -/
lemma real_ineq_53 {N : ℕ} (i j : Fin N) (hij : i ≠ j) (s s' : Fin N → ℝ) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hs : ∀ ℓ, 0 ≤ s ℓ ∧ s ℓ ≤ 1) (hs' : ∀ ℓ, 0 ≤ s' ℓ ∧ s' ℓ ≤ 1) (hsi : s i = 0) :
    (lam • s + (1 - lam) • s') i ^ 2 + ∑ ℓ, (lam • s + (1 - lam) • s') ℓ ^ 2
      ≤ 4 * (1 - lam) ^ 2
        + (1 - lam) * ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), s' ℓ ^ 2
        + lam * (s j ^ 2 + ∑ ℓ, s ℓ ^ 2) := by
  set c := 1 - lam with hc
  have hc0 : 0 ≤ c := by linarith
  have hac : lam + c = 1 := by linarith
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_split i j hij (fun ℓ => (lam * s ℓ + c * s' ℓ) ^ 2),
    sum_split i j hij (fun ℓ => s ℓ ^ 2)]
  simp only [hsi]
  have hi : (lam * 0 + c * s' i) ^ 2 ≤ c ^ 2 := by
    have := hs' i
    have h1 : s' i ^ 2 ≤ 1 := by nlinarith
    rw [mul_zero, zero_add, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg c)]
  have hj := coord_bound_j lam c (s j) (s' j) hlam0 hc0 hac (hs j).1 (hs' j).1 (hs' j).2
  have hrest : ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), (lam * s ℓ + c * s' ℓ) ^ 2
      ≤ ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ i ∧ ℓ ≠ j), (lam * s ℓ ^ 2 + c * s' ℓ ^ 2) := by
    apply Finset.sum_le_sum
    intro ℓ _
    exact coord_bound lam c _ _ hlam0 hc0 hac
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hrest
  nlinarith

/-- Lemma 5.3. -/
theorem lemma_5_3_core {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i j : Fin (N + 1))
    (hij : i ≠ j) (σ : Perm (Fin (N + 1))) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fp A σ i ≤ ENNReal.ofReal (4 * (1 - lam) ^ 2) + ENNReal.ofReal (1 - lam) * g A σ i j
      + ENNReal.ofReal lam * fpm A σ j i := by
  have hc0 : 0 ≤ 1 - lam := by linarith
  rcases iInf_ofReal_cases (V A σ) (V_compact A σ) _ (cont_g i j) with ⟨hV, hg⟩ | ⟨s', hs', hg, hmin'⟩
  · -- V empty: g = ⊤ and fpm = ⊤
    have hfpm : (⨅ s ∈ {s ∈ V A σ | s i = 0}, ENNReal.ofReal (s j ^ 2 + ∑ ℓ, s ℓ ^ 2)) = ⊤ := by
      have : {s ∈ V A σ | s i = 0} = ∅ := by rw [hV]; simp
      simp [this]
    unfold g fpm
    rw [hg, hfpm]
    rcases eq_or_lt_of_le hlam1 with h1 | h1
    · rw [h1]; simp
    · rw [ENNReal.mul_top (by simpa [ENNReal.ofReal_eq_zero] using h1)]; simp
  · rcases iInf_ofReal_cases {s ∈ V A σ | s i = 0} (T_compact A σ i) _ (cont_fp j)
      with ⟨hT, hfpm⟩ | ⟨s, hs, hfpm, hmin⟩
    · unfold g fpm
      rw [hg, hfpm]
      rcases eq_or_lt_of_le hlam0 with h0 | h0
      · subst h0
        simp only [sub_zero, ENNReal.ofReal_one, one_mul, ENNReal.ofReal_zero, zero_mul, add_zero]
        refine (iInf₂_le s' hs').trans ?_
        rw [← ENNReal.ofReal_add (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        rw [sum_split i j hij (fun ℓ => s' ℓ ^ 2)]
        have h1 := V_coord hs' i
        have h2 := V_coord hs' j
        nlinarith
      · rw [ENNReal.mul_top (by simpa [ENNReal.ofReal_eq_zero] using h0)]; simp
    · unfold g fpm
      rw [hg, hfpm]
      have hs'' : lam • s + (1 - lam) • s' ∈ V A σ :=
        V_convex A σ hs.1 hs' hlam0 hc0 (by ring)
      refine (iInf₂_le _ hs'').trans ?_
      rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul hlam0,
        ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg hc0 (Finset.sum_nonneg fun _ _ => sq_nonneg _)),
        ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg hlam0 (by positivity))]
      apply ENNReal.ofReal_le_ofReal
      exact real_ineq_53 i j hij s s' lam hlam0 hlam1 (fun ℓ => V_coord hs.1 ℓ)
        (fun ℓ => V_coord hs' ℓ) hs.2

/-- Lemma 5.7. -/
theorem lemma_5_7_core {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (σ : Perm (Fin (N + 1)))
    (j : Fin (N + 1)) (hj : j ≠ σ (Fin.last N)) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fp A σ (Fin.last N) ≤ ENNReal.ofReal (4 * (1 - lam) ^ 2)
      + ENNReal.ofReal (1 - lam) * g A σ (Fin.last N) (σ⁻¹ j)
      + ENNReal.ofReal lam * fpm A σ (σ⁻¹ j) (Fin.last N) := by
  apply lemma_5_3_core A (Fin.last N) (σ⁻¹ j) _ σ lam hlam0 hlam1
  intro h
  apply hj
  rw [h]; simp



/-- Extension-by-zero / coordinate-reindexing linear map. -/
def extMap {N M : ℕ} (e : Fin M → Option (Fin N)) : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ) where
  toFun s m := (e m).elim 0 s
  map_add' x y := by funext m; cases h : e m <;> simp [h]
  map_smul' c x := by funext m; cases h : e m <;> simp [h]

@[simp] lemma extMap_apply {N M : ℕ} (e : Fin M → Option (Fin N)) (s : Fin N → ℝ) (m : Fin M) :
    extMap e s m = (e m).elim 0 s := rfl

/-- A linear map sending `U` into a convex set sends `V` into it. -/
lemma V_map {N M : ℕ} (B : Set (Perm (Fin N))) (τ : Perm (Fin N))
    (φ : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ)) (W : Set (Fin M → ℝ)) (hW : Convex ℝ W)
    (hU : ∀ s ∈ U B τ, φ s ∈ W) : ∀ s ∈ V B τ, φ s ∈ W :=
  fun s hs => convexHull_min (fun u hu => hU u hu) (hW.linear_preimage φ) hs

lemma convex_T {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (m : Fin N) :
    Convex ℝ {s ∈ V A σ | s m = 0} := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_convexHull ℝ _) hx.1 hy.1 ha hb hab, ?_⟩
  show (a • x + b • y) m = 0
  simp [hx.2, hy.2]

/-- `e'` : drop the last coordinate. -/
def eLast (N : ℕ) : Fin (N + 1) → Option (Fin N) :=
  fun m => if h : m = Fin.last N then none else some (m.castPred h)

@[simp] lemma eLast_castSucc {N : ℕ} (ℓ : Fin N) : eLast N ℓ.castSucc = some ℓ := by
  simp [eLast, Fin.castSucc_ne_last]

@[simp] lemma eLast_last {N : ℕ} : eLast N (Fin.last N) = none := by simp [eLast]

lemma t_t {N : ℕ} (i m : Fin (N + 1)) : t N i (t N i m) = m := swap_apply_self _ _ _

lemma sum_eLast {N : ℕ} (s : Fin N → ℝ) :
    ∑ m, ((eLast N m).elim 0 s) ^ 2 = ∑ ℓ, s ℓ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp

/-- Transfer for Lemma 5.4: for `σ ∈ G_i`, `fpm A σ (t_i(x)) i ≤ fp (R(A_i)) (Rσ) x`. -/
theorem transfer_54 {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i : Fin (N + 1))
    (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G N i)
    (Rσ : Perm (Fin N)) (hRσ : Restricts (σ * t N i) Rσ) (x : Fin N) :
    fpm A σ (t N i x.castSucc) i ≤ fp (RImage A i) Rσ x := by
  have hσi : σ i = Fin.last N := by simpa [G] using hσ
  set φ := extMap (fun m => eLast N (t N i m)) with hφ
  have hval : ∀ s : Fin N → ℝ,
      (φ s) (t N i x.castSucc) ^ 2 + ∑ m, (φ s m) ^ 2 = s x ^ 2 + ∑ ℓ, s ℓ ^ 2 := by
    intro s
    have h1 : (φ s) (t N i x.castSucc) = s x := by
      simp [hφ, t, swap_apply_self]
    have h2 : ∑ m, (φ s m) ^ 2 = ∑ ℓ, s ℓ ^ 2 := by
      rw [← sum_eLast s]
      simp only [hφ, extMap_apply]
      exact Equiv.sum_comp (t N i) (fun n => ((eLast N n).elim 0 s) ^ 2)
    rw [h1, h2]
  have hmap : ∀ s ∈ V (RImage A i) Rσ, φ s ∈ {s ∈ V A σ | s i = 0} := by
    apply V_map _ _ φ _ (convex_T A σ i)
    intro s hs
    obtain ⟨h01, τ, ⟨ρ, hρA, hρi, hρτ⟩, hτ⟩ := hs
    refine ⟨subset_convexHull ℝ _ ⟨fun m => ?_, ρ, hρA, fun m hm => ?_⟩, ?_⟩
    · simp only [hφ, extMap_apply, eLast]
      split_ifs with h
      · simp
      · simpa using h01 _
    · simp only [hφ, extMap_apply, eLast] at hm
      split_ifs at hm with h
      · have : m = i := by
          simpa [t, swap_apply_eq_iff] using h
        rw [this, hσi, hρi]
      · simp only [Option.elim] at hm
        have hτm := hτ _ hm
        have e1 := hρτ ((t N i m).castPred h)
        have e2 := hRσ ((t N i m).castPred h)
        rw [Fin.castSucc_castPred] at e1 e2
        simp only [Perm.mul_apply, t_t] at e1 e2
        rw [e1, e2, hτm]
    · simp [hφ, extMap_apply, eLast, t]
  unfold fpm fp
  refine le_iInf₂ fun s hs => ?_
  refine (iInf₂_le (φ s) (hmap s hs)).trans ?_
  rw [hval]

/-- Lemma 5.4. -/
theorem lemma_5_4_core {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i j : Fin (N + 1))
    (hij : i ≠ j) (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G N i)
    (Rσ : Perm (Fin N)) (hRσ : Restricts (σ * t N i) Rσ)
    (q : Fin N) (hq : q.castSucc = t N i j) :
    fpm A σ j i ≤ fp (RImage A i) Rσ q := by
  have := transfer_54 A i σ hσ Rσ hRσ q
  rwa [hq, show t N i (t N i j) = j from swap_apply_self _ _ _] at this

/-- Transfer for Lemma 5.8: for `σ ∈ G'_i`, `fpm A σ (castSucc x) last ≤ fp (R'(A'_i)) (R'σ) x`. -/
theorem transfer_58 {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i : Fin (N + 1))
    (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G' N i)
    (R'σ : Perm (Fin N)) (hR'σ : Restricts (t N i * σ) R'σ) (x : Fin N) :
    fpm A σ x.castSucc (Fin.last N) ≤ fp (R'Image A i) R'σ x := by
  have hσi : σ (Fin.last N) = i := by simpa [G'] using hσ
  set φ := extMap (eLast N) with hφ
  have hval : ∀ s : Fin N → ℝ,
      (φ s) x.castSucc ^ 2 + ∑ m, (φ s m) ^ 2 = s x ^ 2 + ∑ ℓ, s ℓ ^ 2 := by
    intro s
    have h1 : (φ s) x.castSucc = s x := by simp [hφ]
    have h2 : ∑ m, (φ s m) ^ 2 = ∑ ℓ, s ℓ ^ 2 := by
      rw [← sum_eLast s]
      simp only [hφ, extMap_apply]
    rw [h1, h2]
  have hmap : ∀ s ∈ V (R'Image A i) R'σ, φ s ∈ {s ∈ V A σ | s (Fin.last N) = 0} := by
    apply V_map _ _ φ _ (convex_T A σ (Fin.last N))
    intro s hs
    obtain ⟨h01, τ, ⟨ρ, hρA, hρi, hρτ⟩, hτ⟩ := hs
    refine ⟨subset_convexHull ℝ _ ⟨fun m => ?_, ρ, hρA, fun m hm => ?_⟩, ?_⟩
    · simp only [hφ, extMap_apply, eLast]
      split_ifs with h
      · simp
      · simpa using h01 _
    · simp only [hφ, extMap_apply, eLast] at hm
      split_ifs at hm with h
      · rw [h, hσi, hρi]
      · simp only [Option.elim] at hm
        have hτm := hτ _ hm
        have e1 := hρτ (m.castPred h)
        have e2 := hR'σ (m.castPred h)
        rw [Fin.castSucc_castPred] at e1 e2
        simp only [Perm.mul_apply] at e1 e2
        rw [hτm, ← e2] at e1
        exact (t N i).injective e1
    · simp [hφ, extMap_apply, eLast]
  unfold fpm fp
  refine le_iInf₂ fun s hs => ?_
  refine (iInf₂_le (φ s) (hmap s hs)).trans ?_
  rw [hval]

/-- Lemma 5.8. -/
theorem lemma_5_8_core {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i j : Fin (N + 1))
    (hij : i ≠ j) (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G' N i)
    (R'σ : Perm (Fin N)) (hR'σ : Restricts (t N i * σ) R'σ)
    (q : Fin N) (hq : q.castSucc = t N i j) :
    fpm A σ (σ⁻¹ j) (Fin.last N) ≤ fp (R'Image A i) R'σ (R'σ⁻¹ q) := by
  have hσi : σ (Fin.last N) = i := by simpa [G'] using hσ
  have hy : σ⁻¹ j ≠ Fin.last N := by
    intro h
    apply hij
    rw [← hσi, ← h]; simp
  have hx : (σ⁻¹ j).castPred hy = R'σ⁻¹ q := by
    rw [Perm.eq_inv_iff_eq]
    apply Fin.castSucc_injective
    rw [← hR'σ, Fin.castSucc_castPred, Perm.mul_apply]
    simp [hq]
  have := transfer_58 A i σ hσ R'σ hR'σ ((σ⁻¹ j).castPred hy)
  rwa [Fin.castSucc_castPred, hx] at this


/-! ### Extension of permutations and the bijections `S_N ≃ G_i`, `S_N ≃ G'_i` -/

/-- Extension of `τ ∈ S_N` to `S_{N+1}`, fixing `N + 1`. -/
def extP {N : ℕ} (τ : Perm (Fin N)) : Perm (Fin (N + 1)) :=
  τ.viaFintypeEmbedding Fin.castSuccEmb

@[simp] lemma extP_castSucc {N : ℕ} (τ : Perm (Fin N)) (ℓ : Fin N) :
    extP τ ℓ.castSucc = (τ ℓ).castSucc := by
  have := Equiv.Perm.viaFintypeEmbedding_apply_image τ Fin.castSuccEmb ℓ
  simpa [extP, Fin.castSuccEmb_apply] using this

@[simp] lemma extP_last {N : ℕ} (τ : Perm (Fin N)) : extP τ (Fin.last N) = Fin.last N := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨ℓ, hℓ⟩
  exact Fin.castSucc_ne_last ℓ (by simpa [Fin.castSuccEmb_apply] using hℓ)

lemma restricts_extP {N : ℕ} (τ : Perm (Fin N)) : Restricts (extP τ) τ := fun ℓ => by simp

lemma restricts_unique {N : ℕ} {ρ : Perm (Fin (N + 1))} {τ τ' : Perm (Fin N)}
    (h : Restricts ρ τ) (h' : Restricts ρ τ') : τ = τ' := by
  ext ℓ
  have := (h ℓ).symm.trans (h' ℓ)
  exact congrArg Fin.val (Fin.castSucc_injective _ this)

lemma extP_injective {N : ℕ} : Function.Injective (extP (N := N)) := fun τ τ' h =>
  restricts_unique (restricts_extP τ) (h ▸ restricts_extP τ')

lemma eq_extP_of_restricts {N : ℕ} {ρ : Perm (Fin (N + 1))} (hρ : ρ (Fin.last N) = Fin.last N)
    {τ : Perm (Fin N)} (h : Restricts ρ τ) : ρ = extP τ := by
  ext m
  refine Fin.lastCases ?_ (fun ℓ => ?_) m
  · simp [hρ]
  · simp [h ℓ]

lemma exists_restricts {N : ℕ} (ρ : Perm (Fin (N + 1))) (hρ : ρ (Fin.last N) = Fin.last N) :
    ∃ τ : Perm (Fin N), Restricts ρ τ := by
  have hne : ∀ ℓ : Fin N, ρ ℓ.castSucc ≠ Fin.last N := by
    intro ℓ h
    rw [← hρ] at h
    exact Fin.castSucc_ne_last ℓ (ρ.injective h)
  let f : Fin N → Fin N := fun ℓ => (ρ ℓ.castSucc).castPred (hne ℓ)
  have hf : Function.Injective f := by
    intro a b h
    have : ρ a.castSucc = ρ b.castSucc := by
      have := congrArg Fin.castSucc h
      simpa [f, Fin.castSucc_castPred] using this
    exact Fin.castSucc_injective _ (ρ.injective this)
  refine ⟨Equiv.ofBijective f hf.bijective_of_finite, fun ℓ => ?_⟩
  simp [f, Fin.castSucc_castPred]

/-- `τ ↦ (extP τ) ∘ t_i`, a bijection from `S_N` onto `G_i`. -/
def emb (N : ℕ) (i : Fin (N + 1)) (τ : Perm (Fin N)) : Perm (Fin (N + 1)) := extP τ * t N i

/-- `τ ↦ t_i ∘ (extP τ)`, a bijection from `S_N` onto `G'_i`. -/
def emb' (N : ℕ) (i : Fin (N + 1)) (τ : Perm (Fin N)) : Perm (Fin (N + 1)) := t N i * extP τ

lemma t_mul_t {N : ℕ} (i : Fin (N + 1)) : t N i * t N i = 1 := by
  ext m; simp [t, swap_apply_self]

lemma emb_injective {N : ℕ} (i : Fin (N + 1)) : Function.Injective (emb N i) := by
  intro τ τ' h
  apply extP_injective
  simpa [emb] using congrArg (· * t N i) h

lemma emb'_injective {N : ℕ} (i : Fin (N + 1)) : Function.Injective (emb' N i) := by
  intro τ τ' h
  apply extP_injective
  simpa [emb'] using congrArg (t N i * ·) h

lemma emb_mem_G {N : ℕ} (i : Fin (N + 1)) (τ : Perm (Fin N)) : emb N i τ ∈ G N i := by
  simp [G, emb, t]

lemma emb'_mem_G' {N : ℕ} (i : Fin (N + 1)) (τ : Perm (Fin N)) : emb' N i τ ∈ G' N i := by
  simp [G', emb', t]

lemma restricts_emb {N : ℕ} (i : Fin (N + 1)) (τ : Perm (Fin N)) :
    Restricts (emb N i τ * t N i) τ := by
  rw [emb, mul_assoc, t_mul_t, mul_one]; exact restricts_extP τ

lemma restricts_emb' {N : ℕ} (i : Fin (N + 1)) (τ : Perm (Fin N)) :
    Restricts (t N i * emb' N i τ) τ := by
  rw [emb', ← mul_assoc, t_mul_t, one_mul]; exact restricts_extP τ

lemma G_eq_image {N : ℕ} (i : Fin (N + 1)) : G N i = Finset.univ.image (emb N i) := by
  ext σ
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hσ
    have hσi : σ i = Fin.last N := by simpa [G] using hσ
    obtain ⟨τ, hτ⟩ := exists_restricts (σ * t N i) (by simp [t, hσi])
    refine ⟨τ, ?_⟩
    rw [emb, ← eq_extP_of_restricts (by simp [t, hσi]) hτ, mul_assoc, t_mul_t, mul_one]
  · rintro ⟨τ, rfl⟩; exact emb_mem_G i τ

lemma G'_eq_image {N : ℕ} (i : Fin (N + 1)) : G' N i = Finset.univ.image (emb' N i) := by
  ext σ
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hσ
    have hσi : σ (Fin.last N) = i := by simpa [G'] using hσ
    obtain ⟨τ, hτ⟩ := exists_restricts (t N i * σ) (by simp [t, hσi])
    refine ⟨τ, ?_⟩
    rw [emb', ← eq_extP_of_restricts (by simp [t, hσi]) hτ, ← mul_assoc, t_mul_t, one_mul]
  · rintro ⟨τ, rfl⟩; exact emb'_mem_G' i τ

lemma card_G {N : ℕ} (i : Fin (N + 1)) : (G N i).card = Fintype.card (Perm (Fin N)) := by
  rw [G_eq_image, Finset.card_image_of_injective _ (emb_injective i), Finset.card_univ]

lemma card_G' {N : ℕ} (i : Fin (N + 1)) : (G' N i).card = Fintype.card (Perm (Fin N)) := by
  rw [G'_eq_image, Finset.card_image_of_injective _ (emb'_injective i), Finset.card_univ]

lemma sum_G {N : ℕ} (i : Fin (N + 1)) (F : Perm (Fin (N + 1)) → ℝ≥0∞) :
    ∑ σ ∈ G N i, F σ = ∑ τ, F (emb N i τ) := by
  rw [G_eq_image, Finset.sum_image (fun a _ b _ h => emb_injective i h)]

lemma sum_G' {N : ℕ} (i : Fin (N + 1)) (F : Perm (Fin (N + 1)) → ℝ≥0∞) :
    ∑ σ ∈ G' N i, F σ = ∑ τ, F (emb' N i τ) := by
  rw [G'_eq_image, Finset.sum_image (fun a _ b _ h => emb'_injective i h)]

lemma uniformAvg_G {N : ℕ} (i : Fin (N + 1)) (F : Perm (Fin (N + 1)) → ℝ≥0∞) :
    uniformAvg (G N i) F = uniformAvg Finset.univ (fun τ => F (emb N i τ)) := by
  rw [uniformAvg, uniformAvg, card_G, sum_G, Finset.card_univ]

lemma uniformAvg_G' {N : ℕ} (i : Fin (N + 1)) (F : Perm (Fin (N + 1)) → ℝ≥0∞) :
    uniformAvg (G' N i) F = uniformAvg Finset.univ (fun τ => F (emb' N i τ)) := by
  rw [uniformAvg, uniformAvg, card_G', sum_G', Finset.card_univ]

lemma mem_RImage_iff {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i : Fin (N + 1)) (τ : Perm (Fin N)) :
    τ ∈ RImage A i ↔ emb N i τ ∈ A := by
  constructor
  · rintro ⟨ρ, hρA, hρi, hρτ⟩
    have : ρ * t N i = extP τ := eq_extP_of_restricts (by simp [t, hρi]) hρτ
    have h2 : ρ = emb N i τ := by
      rw [emb, ← this, mul_assoc, t_mul_t, mul_one]
    rwa [← h2]
  · intro h
    exact ⟨emb N i τ, h, by simpa [G] using emb_mem_G i τ, restricts_emb i τ⟩

lemma mem_R'Image_iff {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i : Fin (N + 1)) (τ : Perm (Fin N)) :
    τ ∈ R'Image A i ↔ emb' N i τ ∈ A := by
  constructor
  · rintro ⟨ρ, hρA, hρi, hρτ⟩
    have : t N i * ρ = extP τ := eq_extP_of_restricts (by simp [t, hρi]) hρτ
    have h2 : ρ = emb' N i τ := by
      rw [emb', ← this, ← mul_assoc, t_mul_t, one_mul]
    rwa [← h2]
  · intro h
    exact ⟨emb' N i τ, h, by simpa [G'] using emb'_mem_G' i τ, restricts_emb' i τ⟩

lemma uniformProb_G {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i : Fin (N + 1)) :
    uniformProb (G N i) A = PN (RImage A i) := by
  rw [uniformProb, PN, uniformProb, card_G, Finset.card_univ]
  congr 2
  rw [G_eq_image, Finset.filter_image, Finset.card_image_of_injective _ (emb_injective i)]
  congr 1
  ext τ
  simp [mem_RImage_iff]

lemma uniformProb_G' {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i : Fin (N + 1)) :
    uniformProb (G' N i) A = PN (R'Image A i) := by
  rw [uniformProb, PN, uniformProb, card_G', Finset.card_univ]
  congr 2
  rw [G'_eq_image, Finset.filter_image, Finset.card_image_of_injective _ (emb'_injective i)]
  congr 1
  ext τ
  simp [mem_R'Image_iff]

lemma exp16_mono {a b : ℝ≥0∞} (h : a ≤ b) : exp16 a ≤ exp16 b := by
  unfold exp16
  apply EReal.exp_monotone
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr (by gcongr)

lemma uniformAvg_mono {α : Type*} (S : Finset α) {F G : α → ℝ≥0∞} (h : ∀ x ∈ S, F x ≤ G x) :
    uniformAvg S F ≤ uniformAvg S G := by
  unfold uniformAvg
  gcongr with x hx
  exact h x hx

/-- Corollary 5.5. -/
theorem cor_5_5_core {N : ℕ} (hIH : Ineq53 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hij : i ≠ j) :
    uniformAvg (G N i) (fun σ => exp16 (fpm A σ j i)) ≤ (uniformProb (G N i) A)⁻¹ := by
  have hne : t N i j ≠ Fin.last N := by
    intro h
    have : j = i := by simpa [t, swap_apply_eq_iff] using h
    exact hij this.symm
  set q := (t N i j).castPred hne with hq
  have hqq : q.castSucc = t N i j := Fin.castSucc_castPred _ _
  rw [uniformAvg_G, uniformProb_G]
  refine le_trans (uniformAvg_mono _ fun τ _ => exp16_mono
    (lemma_5_4_core A i j hij (emb N i τ) (emb_mem_G i τ) τ (restricts_emb i τ) q hqq)) ?_
  exact hIH (RImage A i) q

/-- Corollary 5.9. -/
theorem cor_5_9_core {N : ℕ} (hIH : Ineq54 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hji : j ≠ i) :
    uniformAvg (G' N i) (fun σ => exp16 (fpm A σ (σ⁻¹ j) (Fin.last N)))
      ≤ (uniformProb (G' N i) A)⁻¹ := by
  have hne : t N i j ≠ Fin.last N := by
    intro h
    exact hji (by simpa [t, swap_apply_eq_iff] using h)
  set q := (t N i j).castPred hne with hq
  have hqq : q.castSucc = t N i j := Fin.castSucc_castPred _ _
  rw [uniformAvg_G', uniformProb_G']
  refine le_trans (uniformAvg_mono _ fun τ _ => exp16_mono
    (lemma_5_8_core A i j hji.symm (emb' N i τ) (emb'_mem_G' i τ) τ (restricts_emb' i τ) q hqq)) ?_
  exact hIH (R'Image A i) q

end TalagrandConc.SymmetricGroup

open TalagrandConc.SymmetricGroup
open Equiv

theorem solution {N : ℕ} (hIH : Ineq54 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hji : j ≠ i) :
    uniformAvg (G' N i) (fun σ => exp16 (fpm A σ (σ⁻¹ j) (Fin.last N)))
      ≤ (uniformProb (G' N i) A)⁻¹ := by
  exact cor_5_9_core hIH A i j hji
