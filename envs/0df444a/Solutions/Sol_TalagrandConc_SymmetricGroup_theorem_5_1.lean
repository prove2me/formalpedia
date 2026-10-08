-- Prove2me | solution 1 for TalagrandConc.SymmetricGroup.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:36:37.619824+00:00
-- url     : https://prove2.me/submissions/c8920c47-3711-4d97-b428-35b1eaddb546

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


/-! ### `g` is dominated by `fpm` of a nearby permutation -/

/-- Set coordinates `a`, `b` to `1`. -/
def setOne {N : ℕ} (a b : Fin N) (s : Fin N → ℝ) : Fin N → ℝ :=
  fun m => if m = a ∨ m = b then 1 else s m

lemma setOne_mem_V {N : ℕ} (A : Set (Perm (Fin N))) (σ σ' : Perm (Fin N)) (a b : Fin N)
    (hagree : ∀ m, m ≠ a → m ≠ b → σ m = σ' m) :
    ∀ s ∈ V A σ', setOne a b s ∈ V A σ := by
  intro s hs
  have hconv : Convex ℝ {s : Fin N → ℝ | setOne a b s ∈ V A σ} := by
    intro x hx y hy α β hα hβ hαβ
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have : setOne a b (α • x + β • y) = α • setOne a b x + β • setOne a b y := by
      funext m
      simp only [setOne, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs
      · linarith
      · rfl
    rw [this]
    exact (convex_convexHull ℝ _) hx hy hα hβ hαβ
  refine convexHull_min ?_ hconv hs
  intro u hu
  obtain ⟨h01, τ, hτA, hτ⟩ := hu
  refine subset_convexHull ℝ _ ⟨fun m => ?_, τ, hτA, fun m hm => ?_⟩
  · simp only [setOne]
    split_ifs
    · simp
    · exact h01 m
  · simp only [setOne] at hm
    split_ifs at hm with h
    · norm_num at hm
    · push_neg at h
      rw [hτ m hm, hagree m h.1 h.2]

lemma g_le_fpm_general {N : ℕ} (A : Set (Perm (Fin N))) (σ σ' : Perm (Fin N)) (a b : Fin N)
    (hagree : ∀ m, m ≠ a → m ≠ b → σ m = σ' m) (p c : Fin N) :
    g A σ a b ≤ fpm A σ' p c := by
  unfold g fpm
  refine le_iInf₂ fun s hs => ?_
  refine (iInf₂_le (setOne a b s) (setOne_mem_V A σ σ' a b hagree s hs.1)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have e : ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ a ∧ ℓ ≠ b), setOne a b s ℓ ^ 2
      = ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ a ∧ ℓ ≠ b), s ℓ ^ 2 := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    simp [setOne, hℓ.1, hℓ.2]
  rw [e]
  have h1 : ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ≠ a ∧ ℓ ≠ b), s ℓ ^ 2 ≤ ∑ ℓ, s ℓ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  nlinarith [sq_nonneg (s p)]

/-! ### Reindexing between sections -/

lemma G_map {N : ℕ} (i j : Fin (N + 1)) :
    G N i = (G N j).map (Equiv.mulRight (swap i j)).toEmbedding := by
  ext σ
  rw [Finset.mem_map_equiv]
  simp [G, Perm.mul_apply]

lemma G'_map {N : ℕ} (i j : Fin (N + 1)) :
    G' N i = (G' N j).map (Equiv.mulLeft (swap i j)).toEmbedding := by
  ext σ
  rw [Finset.mem_map_equiv]
  simp [G', Perm.mul_apply, swap_apply_eq_iff]

lemma uniformAvg_G_swap {N : ℕ} (i j : Fin (N + 1)) (F : Perm (Fin (N + 1)) → ℝ≥0∞) :
    uniformAvg (G N i) F = uniformAvg (G N j) (fun σ => F (σ * swap i j)) := by
  rw [uniformAvg, uniformAvg, card_G, card_G, G_map i j, Finset.sum_map]
  rfl

lemma uniformAvg_G'_swap {N : ℕ} (i j : Fin (N + 1)) (F : Perm (Fin (N + 1)) → ℝ≥0∞) :
    uniformAvg (G' N i) F = uniformAvg (G' N j) (fun σ => F (swap i j * σ)) := by
  rw [uniformAvg, uniformAvg, card_G', card_G', G'_map i j, Finset.sum_map]
  rfl

lemma exists_fin_of_ne {N : ℕ} {i j : Fin (N + 1)} (hij : i ≠ j) : Nonempty (Fin N) := by
  cases N with
  | zero => exact absurd (Fin.ext (by omega)) hij
  | succ n => exact ⟨0⟩

/-- Lemma 5.6. -/
theorem lemma_5_6_core {N : ℕ} (hIH : Ineq53 N ∨ Ineq54 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hji : j ≠ i) :
    uniformAvg (G N i) (fun σ => exp16 (g A σ i j)) ≤ (uniformProb (G N j) A)⁻¹ := by
  rw [uniformAvg_G_swap i j, uniformAvg_G, uniformProb_G]
  have hagree : ∀ τ : Perm (Fin N), ∀ m, m ≠ i → m ≠ j →
      (emb N j τ * swap i j) m = emb N j τ m := by
    intro τ m hmi hmj
    simp [Perm.mul_apply, swap_apply_of_ne_of_ne hmi hmj]
  rcases hIH with h53 | h54
  · have hne : t N j i ≠ Fin.last N := by
      intro h
      have : i = j := by simpa [t, swap_apply_eq_iff] using h
      exact hji this.symm
    set x := (t N j i).castPred hne with hx
    refine le_trans (uniformAvg_mono _ fun τ _ => exp16_mono ?_) (h53 (RImage A j) x)
    refine (g_le_fpm_general A _ _ i j (hagree τ) (t N j x.castSucc) j).trans ?_
    exact transfer_54 A j (emb N j τ) (emb_mem_G j τ) τ (restricts_emb j τ) x
  · obtain ⟨x⟩ := exists_fin_of_ne hji
    refine le_trans (uniformAvg_mono _ fun τ _ => exp16_mono ?_) (h54 (RImage A j) x)
    refine (g_le_fpm_general A _ _ i j (hagree τ) (t N j (τ⁻¹ x).castSucc) j).trans ?_
    exact transfer_54 A j (emb N j τ) (emb_mem_G j τ) τ (restricts_emb j τ) (τ⁻¹ x)

/-- Lemma 5.10. -/
theorem lemma_5_10_core {N : ℕ} (hIH : Ineq53 N ∨ Ineq54 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hij : i ≠ j) :
    uniformAvg (G' N i) (fun σ => exp16 (g A σ (Fin.last N) (σ⁻¹ j)))
      ≤ (uniformProb (G' N j) A)⁻¹ := by
  rw [uniformAvg_G'_swap i j, uniformAvg_G', uniformProb_G']
  have hagree : ∀ τ : Perm (Fin N), ∀ m, m ≠ Fin.last N → m ≠ (swap i j * emb' N j τ)⁻¹ j →
      (swap i j * emb' N j τ) m = emb' N j τ m := by
    intro τ m hm1 hm2
    have hlast : emb' N j τ (Fin.last N) = j := by simpa [G'] using emb'_mem_G' j τ
    simp only [Perm.mul_apply]
    apply swap_apply_of_ne_of_ne
    · intro h
      apply hm2
      rw [Perm.eq_inv_iff_eq, Perm.mul_apply, h, swap_apply_left]
    · intro h
      apply hm1
      exact (emb' N j τ).injective (h.trans hlast.symm)
  obtain ⟨x0⟩ := exists_fin_of_ne hij
  rcases hIH with h53 | h54
  · refine le_trans (uniformAvg_mono _ fun τ _ => exp16_mono ?_) (h53 (R'Image A j) x0)
    refine (g_le_fpm_general A _ _ _ _ (hagree τ) x0.castSucc (Fin.last N)).trans ?_
    exact transfer_58 A j (emb' N j τ) (emb'_mem_G' j τ) τ (restricts_emb' j τ) x0
  · refine le_trans (uniformAvg_mono _ fun τ _ => exp16_mono ?_) (h54 (R'Image A j) x0)
    refine (g_le_fpm_general A _ _ _ _ (hagree τ) (τ⁻¹ x0).castSucc (Fin.last N)).trans ?_
    exact transfer_58 A j (emb' N j τ) (emb'_mem_G' j τ) τ (restricts_emb' j τ) (τ⁻¹ x0)


/-! ### Analytic lemmas: `exp16`, Hölder, the key inequality -/

lemma exp16_add (x y : ℝ≥0∞) : exp16 (x + y) = exp16 x * exp16 y := by
  unfold exp16
  rw [ENNReal.add_div, EReal.coe_ennreal_add, EReal.exp_add]

lemma exp16_ofReal (c : ℝ) (hc : 0 ≤ c) :
    exp16 (ENNReal.ofReal c) = ENNReal.ofReal (Real.exp (c / 16)) := by
  unfold exp16
  have : ENNReal.ofReal c / 16 = ENNReal.ofReal (c / 16) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [this, EReal.coe_ennreal_ofReal, max_eq_left (by positivity), EReal.exp_coe]

lemma exp16_top : exp16 ⊤ = ⊤ := by
  unfold exp16
  rw [ENNReal.top_div]
  simp

lemma exp16_zero : exp16 0 = 1 := by
  unfold exp16
  simp

lemma exp16_mul_ofReal (μ : ℝ) (hμ : 0 ≤ μ) (z : ℝ≥0∞) :
    exp16 (ENNReal.ofReal μ * z) = exp16 z ^ μ := by
  rcases eq_or_ne z ⊤ with hz | hz
  · subst hz
    rcases eq_or_lt_of_le hμ with h0 | h0
    · subst h0; simp [exp16_zero]
    · rw [ENNReal.mul_top (by simpa [ENNReal.ofReal_eq_zero] using h0), exp16_top,
        ENNReal.top_rpow_of_pos h0]
  · have hx : z = ENNReal.ofReal z.toReal := (ENNReal.ofReal_toReal hz).symm
    rw [hx, ← ENNReal.ofReal_mul hμ, exp16_ofReal _ (by positivity),
      exp16_ofReal _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hμ, ← Real.exp_mul]
    congr 2
    ring

lemma exp16_bound (F Gf Hf : ℝ≥0∞) (c l : ℝ) (hc : 0 ≤ c) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (h : F ≤ ENNReal.ofReal c + ENNReal.ofReal (1 - l) * Gf + ENNReal.ofReal l * Hf) :
    exp16 F ≤ ENNReal.ofReal (Real.exp (c / 16)) * exp16 Gf ^ (1 - l) * exp16 Hf ^ l := by
  refine (exp16_mono h).trans ?_
  rw [exp16_add, exp16_add, exp16_ofReal c hc, exp16_mul_ofReal _ (by linarith),
    exp16_mul_ofReal _ hl0]

lemma uniformAvg_const_mul {α : Type*} (S : Finset α) (k : ℝ≥0∞) (F : α → ℝ≥0∞) :
    uniformAvg S (fun x => k * F x) = k * uniformAvg S F := by
  unfold uniformAvg
  rw [← Finset.mul_sum, mul_left_comm]

/-- Hölder's inequality for uniform averages. -/
lemma uniformAvg_holder {α : Type*} (S : Finset α) (f g : α → ℝ≥0∞) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    uniformAvg S (fun x => f x * g x)
      ≤ (uniformAvg S (fun x => f x ^ p)) ^ (1 / p) * (uniformAvg S (fun x => g x ^ q)) ^ (1 / q) := by
  unfold uniformAvg
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp
  set c : ℝ≥0∞ := ((S.card : ℝ≥0∞))⁻¹ with hc
  have hc0 : c ≠ 0 := by simp [hc]
  have hct : c ≠ ⊤ := by
    simp [hc, Finset.card_pos.mpr hS, Finset.card_ne_zero.mpr hS]
  have hsum : 1 / p + 1 / q = 1 := by
    have := hpq.inv_add_inv_eq_one
    simpa [one_div] using this
  have hcc : c = c ^ (1 / p) * c ^ (1 / q) := by
    rw [← ENNReal.rpow_add _ _ hc0 hct, hsum, ENNReal.rpow_one]
  calc c * ∑ x ∈ S, f x * g x
      ≤ c * ((∑ x ∈ S, f x ^ p) ^ (1 / p) * (∑ x ∈ S, g x ^ q) ^ (1 / q)) := by
        gcongr
        exact ENNReal.inner_le_Lp_mul_Lq S f g hpq
    _ = (c ^ (1 / p) * c ^ (1 / q)) * ((∑ x ∈ S, f x ^ p) ^ (1 / p) * (∑ x ∈ S, g x ^ q) ^ (1 / q)) := by
        rw [← hcc]
    _ = (c ^ (1 / p) * (∑ x ∈ S, f x ^ p) ^ (1 / p)) *
          (c ^ (1 / q) * (∑ x ∈ S, g x ^ q) ^ (1 / q)) := by ring
    _ = _ := by
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hpq.one_div_pos.le,
          ← ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.one_div_pos.le]

/-- Taylor bound: `exp v ≤ 1 + v + v^2/2 + v^3/6 + 5 v^4/96` for `0 ≤ v ≤ 1`. -/
lemma exp_upper4 (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    Real.exp v ≤ 1 + v + v ^ 2 / 2 + v ^ 3 / 6 + 5 * v ^ 4 / 96 := by
  have h := Real.exp_bound (x := v) (by rw [abs_of_nonneg h0]; exact h1) (n := 4) (by norm_num)
  rw [abs_of_nonneg h0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).2
  nlinarith

/-- Taylor bound: `exp (-u) ≤ 1 - u + u^2/2 - u^3/6 + u^4/24 + u^5/100` for `0 ≤ u ≤ 1`. -/
lemma exp_neg_upper5 (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 100 := by
  have h := Real.exp_bound (x := -u) (by rw [abs_neg, abs_of_nonneg h0]; exact h1) (n := 5) (by norm_num)
  rw [abs_neg, abs_of_nonneg h0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := (abs_le.mp h).2
  nlinarith

lemma key_real (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    Real.exp (u - u ^ 2) ≤ 2 - Real.exp (-u) := by
  have hv0 : 0 ≤ u - u ^ 2 := by nlinarith
  have hv1 : u - u ^ 2 ≤ 1 := by nlinarith
  have hA := exp_upper4 (u - u ^ 2) hv0 hv1
  have hB := exp_neg_upper5 u h0 (by linarith)
  have hu2 : u ^ 2 ≤ 1 / 4 := by nlinarith
  have hu3 : u ^ 3 ≤ 1 / 8 := by nlinarith
  have hu4 : u ^ 4 ≤ 1 / 16 := by nlinarith
  have hu5 : u ^ 5 ≤ 1 / 32 := by nlinarith
  have hbr : 0 ≤ 2400 - 225 * u - 724 * u ^ 2 - 350 * u ^ 3 + 500 * u ^ 4 - 125 * u ^ 5 := by
    nlinarith
  have hu3' : 0 ≤ u ^ 3 := by positivity
  have hd : 0 ≤ u ^ 3 * (2400 - 225 * u - 724 * u ^ 2 - 350 * u ^ 3 + 500 * u ^ 4 - 125 * u ^ 5) :=
    mul_nonneg hu3' hbr
  nlinarith

lemma exp_quarter_le : Real.exp (1 / 4) ≤ 4 / 3 := by
  have h := Real.add_one_le_exp (-1 / 4)
  have h2 : Real.exp (1 / 4) * Real.exp (-1 / 4) = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 4)]

/-- The optimisation over `λ`, in the form used by `section_bound`. -/
lemma inf_bound (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧
      Real.exp ((1 - l) ^ 2 / 4) * b⁻¹ ^ (1 - l) * a⁻¹ ^ l ≤ (2 - a / b) / b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set r := a / b with hr
  have hr0 : 0 < r := div_pos ha hb
  have hr1 : r ≤ 1 := (div_le_one hb).mpr hab
  rcases le_or_gt r (Real.exp (-1 / 2)) with hsmall | hbig
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    simp only [sub_zero, one_pow, Real.rpow_one, Real.rpow_zero, mul_one]
    rw [div_eq_mul_inv (2 - r) b]
    gcongr
    have e2 : Real.exp (-1 / 2) ≤ 2 / 3 := by
      have h := Real.add_one_le_exp (1 / 2)
      have h2 : Real.exp (1 / 2) * Real.exp (-1 / 2) = 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos (-1 / 2)]
    linarith [exp_quarter_le]
  · have hlog_le : Real.log r ≤ 0 := Real.log_nonpos hr0.le hr1
    have hlog_gt : -1 / 2 < Real.log r := by
      have := Real.log_lt_log (Real.exp_pos _) hbig
      rwa [Real.log_exp] at this
    set u : ℝ := -Real.log r with hu
    have hu0 : 0 ≤ u := by rw [hu]; linarith
    have hu1 : u ≤ 1 / 2 := by rw [hu]; linarith
    refine ⟨1 - 2 * u, by linarith, by linarith, ?_⟩
    have hr_eq : r = Real.exp (-u) := by
      rw [hu, neg_neg, Real.exp_log hr0]
    have hlogr : Real.log r = Real.log a - Real.log b := Real.log_div ha.ne' hb.ne'
    rw [Real.rpow_def_of_pos (inv_pos.mpr hb), Real.rpow_def_of_pos (inv_pos.mpr ha),
      Real.log_inv, Real.log_inv, ← Real.exp_add, ← Real.exp_add]
    have harg : (1 - (1 - 2 * u)) ^ 2 / 4 + -Real.log b * (1 - (1 - 2 * u)) + -Real.log a * (1 - 2 * u)
        = (u - u ^ 2) + -Real.log b := by
      have : Real.log a = -u + Real.log b := by rw [hu]; linarith
      rw [this]; ring
    rw [harg, Real.exp_add, Real.exp_neg, Real.exp_log hb, div_eq_mul_inv (2 - r) b]
    gcongr
    rw [hr_eq]
    exact key_real u hu0 hu1

/-- The bound for one section. -/
lemma section_bound {α : Type*} (S : Finset α) (F Gf Hf : α → ℝ≥0∞)
    (hFGH : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 → ∀ σ ∈ S,
      F σ ≤ ENNReal.ofReal (4 * (1 - lam) ^ 2) + ENNReal.ofReal (1 - lam) * Gf σ
        + ENNReal.ofReal lam * Hf σ)
    (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b)
    (hG : uniformAvg S (fun σ => exp16 (Gf σ)) ≤ (ENNReal.ofReal b)⁻¹)
    (hH : uniformAvg S (fun σ => exp16 (Hf σ)) ≤ (ENNReal.ofReal a)⁻¹) :
    uniformAvg S (fun σ => exp16 (F σ)) ≤ ENNReal.ofReal ((2 - a / b) / b) := by
  -- the bound for each `l`
  have hl : ∀ l : ℝ, 0 ≤ l → l ≤ 1 →
      uniformAvg S (fun σ => exp16 (F σ)) ≤
        ENNReal.ofReal (Real.exp ((1 - l) ^ 2 / 4)) *
          (uniformAvg S (fun σ => exp16 (Gf σ))) ^ (1 - l) *
          (uniformAvg S (fun σ => exp16 (Hf σ))) ^ l := by
    intro l hl0 hl1
    have hpt : ∀ σ ∈ S, exp16 (F σ) ≤
        ENNReal.ofReal (Real.exp ((1 - l) ^ 2 / 4)) * (exp16 (Gf σ) ^ (1 - l) * exp16 (Hf σ) ^ l) := by
      intro σ hσ
      have := exp16_bound (F σ) (Gf σ) (Hf σ) (4 * (1 - l) ^ 2) l (by positivity) hl0 hl1
        (hFGH l hl0 hl1 σ hσ)
      rw [mul_assoc] at this
      have e : 4 * (1 - l) ^ 2 / 16 = (1 - l) ^ 2 / 4 := by ring
      rw [e] at this
      exact this
    refine (uniformAvg_mono S hpt).trans ?_
    rw [uniformAvg_const_mul, mul_assoc]
    gcongr
    rcases eq_or_lt_of_le hl0 with h0 | h0
    · subst h0
      simp only [sub_zero, ENNReal.rpow_one, ENNReal.rpow_zero, mul_one]
      exact le_rfl
    rcases eq_or_lt_of_le hl1 with h1 | h1
    · subst h1
      simp only [sub_self, ENNReal.rpow_one, ENNReal.rpow_zero, one_mul]
      exact le_rfl
    have hpq : (1 - l)⁻¹.HolderConjugate l⁻¹ := Real.HolderConjugate.one_sub_inv_inv h0 h1
    have := uniformAvg_holder S (fun σ => exp16 (Gf σ) ^ (1 - l)) (fun σ => exp16 (Hf σ) ^ l) hpq
    have e1 : ∀ σ, (exp16 (Gf σ) ^ (1 - l)) ^ (1 - l)⁻¹ = exp16 (Gf σ) := by
      intro σ
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (by linarith), ENNReal.rpow_one]
    have e2 : ∀ σ, (exp16 (Hf σ) ^ l) ^ l⁻¹ = exp16 (Hf σ) := by
      intro σ
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (by linarith), ENNReal.rpow_one]
    simp only [e1, e2, one_div, inv_inv] at this
    exact this
  rcases eq_or_lt_of_le ha0 with ha | ha
  · -- `a = 0`: use `l = 0`
    subst ha
    have := hl 0 le_rfl zero_le_one
    simp only [sub_zero, one_pow, ENNReal.rpow_one, ENNReal.rpow_zero, mul_one] at this
    refine this.trans ?_
    calc ENNReal.ofReal (Real.exp (1 / 4)) * uniformAvg S (fun σ => exp16 (Gf σ))
        ≤ ENNReal.ofReal (Real.exp (1 / 4)) * (ENNReal.ofReal b)⁻¹ := mul_le_mul' le_rfl hG
      _ = ENNReal.ofReal (Real.exp (1 / 4) * b⁻¹) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_inv_of_pos hb]
      _ ≤ ENNReal.ofReal ((2 - 0 / b) / b) := by
        apply ENNReal.ofReal_le_ofReal
        rw [show (2 - 0 / b) / b = 2 * b⁻¹ by ring]
        exact mul_le_mul_of_nonneg_right (by linarith [exp_quarter_le]) (inv_nonneg.mpr hb.le)
  · obtain ⟨l, hl0, hl1, hle⟩ := inf_bound a b ha hab
    refine (hl l hl0 hl1).trans ?_
    calc ENNReal.ofReal (Real.exp ((1 - l) ^ 2 / 4)) *
          (uniformAvg S (fun σ => exp16 (Gf σ))) ^ (1 - l) *
          (uniformAvg S (fun σ => exp16 (Hf σ))) ^ l
        ≤ ENNReal.ofReal (Real.exp ((1 - l) ^ 2 / 4)) *
          ((ENNReal.ofReal b)⁻¹) ^ (1 - l) * ((ENNReal.ofReal a)⁻¹) ^ l := by
          gcongr
      _ = ENNReal.ofReal (Real.exp ((1 - l) ^ 2 / 4) * b⁻¹ ^ (1 - l) * a⁻¹ ^ l) := by
          rw [← ENNReal.ofReal_inv_of_pos hb, ← ENNReal.ofReal_inv_of_pos ha,
            ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hb), ENNReal.ofReal_rpow_of_pos (inv_pos.mpr ha),
            ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Real.exp ((1 - l) ^ 2 / 4) * b⁻¹ ^ (1 - l)),
            ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal ((2 - a / b) / b) := ENNReal.ofReal_le_ofReal hle

/-- Averaging the section bounds. -/
lemma combine_sections {ι : Type*} [Fintype ι] [Nonempty ι] (F a : ι → ℝ≥0∞) (α : ι → ℝ)
    (hα : ∀ i, a i = ENNReal.ofReal (α i)) (hα0 : ∀ i, 0 ≤ α i) (β : ℝ) (hβ : 0 < β)
    (hαβ : ∀ i, α i ≤ β) (hF : ∀ i, F i ≤ ENNReal.ofReal ((2 - α i / β) / β)) :
    ((Fintype.card ι : ℝ≥0∞))⁻¹ * ∑ i, F i ≤ (((Fintype.card ι : ℝ≥0∞))⁻¹ * ∑ i, a i)⁻¹ := by
  set n : ℕ := Fintype.card ι with hn
  have hn0 : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hninv : ((n : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hnR, ENNReal.ofReal_natCast]
  set x : ℝ := (n : ℝ)⁻¹ * ∑ i, α i with hx
  have hsa : ∑ i, a i = ENNReal.ofReal (∑ i, α i) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hα0 i)]
    exact Finset.sum_congr rfl (fun i _ => hα i)
  have hx0 : 0 ≤ x := by
    rw [hx]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hα0 i)
  have hxβ : x ≤ β := by
    rw [hx]
    have : ∑ i, α i ≤ ∑ _i : ι, β := Finset.sum_le_sum fun i _ => hαβ i
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    calc (n : ℝ)⁻¹ * ∑ i, α i ≤ (n : ℝ)⁻¹ * (n * β) := by gcongr
      _ = β := by field_simp
  rw [hsa, hninv, ← ENNReal.ofReal_mul (by positivity), ← hx]
  calc ENNReal.ofReal (n : ℝ)⁻¹ * ∑ i, F i
      ≤ ENNReal.ofReal (n : ℝ)⁻¹ * ∑ i, ENNReal.ofReal ((2 - α i / β) / β) := by
        gcongr with i
        exact hF i
    _ = ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i, (2 - α i / β) / β) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
          have := hαβ i
          have : α i / β ≤ 1 := (div_le_one hβ).mpr this
          apply div_nonneg _ hβ.le; linarith), ← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal ((2 - x / β) / β) := by
        congr 1
        have hs : ∑ i, (2 - α i / β) / β = (2 * n - (∑ i, α i) / β) / β := by
          rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← hn,
            nsmul_eq_mul, Finset.sum_div]
          ring
        rw [hs, hx]
        field_simp
        try ring
    _ ≤ (ENNReal.ofReal x)⁻¹ := by
        rcases eq_or_lt_of_le hx0 with h0 | h0
        · rw [← h0]; simp
        · rw [← ENNReal.ofReal_inv_of_pos h0]
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_iff₀ hβ, inv_mul_eq_div, le_div_iff₀ h0]
          have key : (2 - x / β) * x = β - β * (1 - x / β) ^ 2 := by
            field_simp
            ring
          rw [key]
          nlinarith [mul_nonneg hβ.le (sq_nonneg (1 - x / β))]


/-! ### Decomposition into sections -/

lemma uniformAvg_congr {α : Type*} (S : Finset α) {F G : α → ℝ≥0∞} (h : ∀ x ∈ S, F x = G x) :
    uniformAvg S F = uniformAvg S G := by
  unfold uniformAvg
  rw [Finset.sum_congr rfl h]

lemma uniformProb_eq_avg {α : Type*} (S : Finset α) (A : Set α) :
    uniformProb S A = uniformAvg S (fun x => if x ∈ A then 1 else 0) := by
  unfold uniformProb uniformAvg
  congr 1
  rw [Finset.sum_boole (fun x => x ∈ A) S]

lemma uniformProb_ne_top {α : Type*} (S : Finset α) (A : Set α) : uniformProb S A ≠ ⊤ := by
  unfold uniformProb
  rcases S.eq_empty_or_nonempty with h | h
  · subst h; simp
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by simp [Finset.card_ne_zero.mpr h]))
      (ENNReal.natCast_ne_top _)

lemma uniformProb_le_one {α : Type*} (S : Finset α) (A : Set α) : uniformProb S A ≤ 1 := by
  unfold uniformProb
  rcases S.eq_empty_or_nonempty with h | h
  · subst h; simp
  · calc _ ≤ ((S.card : ℝ≥0∞))⁻¹ * (S.card : ℝ≥0∞) := by
          gcongr
          exact Finset.filter_subset _ _
      _ = 1 := ENNReal.inv_mul_cancel (by simp [Finset.card_ne_zero.mpr h])
          (ENNReal.natCast_ne_top _)

lemma G_filter {N : ℕ} (i : Fin (N + 1)) :
    Finset.univ.filter (fun σ : Perm (Fin (N + 1)) => σ⁻¹ (Fin.last N) = i) = G N i := by
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, G]
  rw [Perm.inv_def, Equiv.symm_apply_eq, eq_comm]

lemma G'_filter {N : ℕ} (i : Fin (N + 1)) :
    Finset.univ.filter (fun σ : Perm (Fin (N + 1)) => σ (Fin.last N) = i) = G' N i := by
  ext σ
  simp [G']

lemma sum_univ_G {N : ℕ} (F : Perm (Fin (N + 1)) → ℝ≥0∞) :
    ∑ σ, F σ = ∑ i, ∑ σ ∈ G N i, F σ := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := fun σ : Perm (Fin (N + 1)) => σ⁻¹ (Fin.last N)) (fun _ _ => Finset.mem_univ _) F]
  exact Finset.sum_congr rfl fun i _ => by rw [G_filter]

lemma sum_univ_G' {N : ℕ} (F : Perm (Fin (N + 1)) → ℝ≥0∞) :
    ∑ σ, F σ = ∑ i, ∑ σ ∈ G' N i, F σ := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := fun σ : Perm (Fin (N + 1)) => σ (Fin.last N)) (fun _ _ => Finset.mem_univ _) F]
  exact Finset.sum_congr rfl fun i _ => by rw [G'_filter]

lemma card_perm_succ (N : ℕ) :
    (Fintype.card (Perm (Fin (N + 1))) : ℝ≥0∞) = ((N + 1 : ℕ) : ℝ≥0∞) * Fintype.card (Perm (Fin N)) := by
  rw [Fintype.card_perm, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin, Nat.factorial_succ]
  push_cast
  ring

lemma uniformAvg_univ_G {N : ℕ} (F : Perm (Fin (N + 1)) → ℝ≥0∞) :
    uniformAvg Finset.univ F = ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, uniformAvg (G N i) F := by
  unfold uniformAvg
  rw [Finset.card_univ, card_perm_succ, sum_univ_G,
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (ENNReal.natCast_ne_top _)), mul_assoc,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [card_G]

lemma uniformAvg_univ_G' {N : ℕ} (F : Perm (Fin (N + 1)) → ℝ≥0∞) :
    uniformAvg Finset.univ F = ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, uniformAvg (G' N i) F := by
  unfold uniformAvg
  rw [Finset.card_univ, card_perm_succ, sum_univ_G',
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (ENNReal.natCast_ne_top _)), mul_assoc,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [card_G']

lemma PN_eq_sections {N : ℕ} (A : Set (Perm (Fin (N + 1)))) :
    PN A = ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, uniformProb (G N i) A := by
  rw [PN, uniformProb_eq_avg, uniformAvg_univ_G]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (uniformProb_eq_avg _ _).symm

lemma PN_eq_sections' {N : ℕ} (A : Set (Perm (Fin (N + 1)))) :
    PN A = ((N + 1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ i, uniformProb (G' N i) A := by
  rw [PN, uniformProb_eq_avg, uniformAvg_univ_G']
  congr 1
  exact Finset.sum_congr rfl fun i _ => (uniformProb_eq_avg _ _).symm

/-! ### Symmetries -/

lemma PN_image {N : ℕ} (e : Perm (Fin N) ≃ Perm (Fin N)) (A : Set (Perm (Fin N))) :
    PN (e '' A) = PN A := by
  unfold PN uniformProb
  congr 2
  have : Finset.univ.filter (fun x => x ∈ e '' A)
      = (Finset.univ.filter (fun x => x ∈ A)).map e.toEmbedding := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_toEmbedding,
      Set.mem_image]
  rw [this, Finset.card_map]

lemma uniformAvg_univ_equiv {N : ℕ} (e : Perm (Fin N) ≃ Perm (Fin N)) (F : Perm (Fin N) → ℝ≥0∞) :
    uniformAvg Finset.univ (fun σ => F (e σ)) = uniformAvg Finset.univ F := by
  unfold uniformAvg
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma fp_le_mul_left {N : ℕ} (π : Perm (Fin N)) (A : Set (Perm (Fin N))) (σ : Perm (Fin N))
    (p : Fin N) : fp A σ p ≤ fp ((Equiv.mulLeft π) '' A) (π * σ) p := by
  have hU : U ((Equiv.mulLeft π) '' A) (π * σ) ⊆ U A σ := by
    rintro s ⟨h01, τ', ⟨τ, hτ, rfl⟩, hagree⟩
    refine ⟨h01, τ, hτ, fun ℓ hℓ => π.injective ?_⟩
    simpa [Perm.mul_apply] using hagree ℓ hℓ
  unfold fp
  exact le_iInf₂ fun s hs => iInf₂_le s (convexHull_mono hU hs)

lemma fp_le_mul_right {N : ℕ} (π : Perm (Fin N)) (A : Set (Perm (Fin N))) (σ : Perm (Fin N))
    (p : Fin N) : fp A σ p ≤ fp ((Equiv.mulRight π) '' A) (σ * π) (π⁻¹ p) := by
  set L : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := LinearMap.funLeft ℝ ℝ (⇑π⁻¹) with hL
  have hLapp : ∀ s m, L s m = s (π⁻¹ m) := fun s m => rfl
  have hmap : ∀ s ∈ V ((Equiv.mulRight π) '' A) (σ * π), L s ∈ V A σ := by
    apply V_map _ _ L _ (convex_convexHull ℝ _)
    rintro s ⟨h01, τ', ⟨τ, hτ, rfl⟩, hagree⟩
    refine subset_convexHull ℝ _ ⟨fun m => h01 _, τ, hτ, fun m hm => ?_⟩
    have := hagree (π⁻¹ m) hm
    simpa [Perm.mul_apply] using this
  unfold fp
  refine le_iInf₂ fun s hs => ?_
  refine (iInf₂_le (L s) (hmap s hs)).trans (le_of_eq ?_)
  congr 1
  simp only [hLapp]
  congr 1
  exact Equiv.sum_comp π⁻¹ (fun ℓ => s ℓ ^ 2)

set_option maxHeartbeats 800000 in
lemma ineq54_of_last {N : ℕ}
    (h : ∀ A : Set (Perm (Fin (N + 1))),
      uniformAvg Finset.univ (fun σ => exp16 (fp A σ (σ⁻¹ (Fin.last N)))) ≤ (PN A)⁻¹) :
    Ineq54 (N + 1) := by
  intro A p
  set π : Perm (Fin (N + 1)) := swap p (Fin.last N) with hπ
  have hπl : π⁻¹ (Fin.last N) = p := by rw [hπ, swap_inv, swap_apply_right]
  set A' : Set (Perm (Fin (N + 1))) := (Equiv.mulLeft π) '' A with hA'
  have e1 := uniformAvg_univ_equiv (Equiv.mulLeft π) (fun σ => exp16 (fp A' σ (σ⁻¹ (Fin.last N))))
  simp only [Equiv.coe_mulLeft] at e1
  have step1 : uniformAvg Finset.univ (fun σ => exp16 (fp A σ (σ⁻¹ p)))
      ≤ uniformAvg Finset.univ (fun σ => exp16 (fp A' (π * σ) ((π * σ)⁻¹ (Fin.last N)))) := by
    apply uniformAvg_mono
    intro σ _
    apply exp16_mono
    have : (π * σ)⁻¹ (Fin.last N) = σ⁻¹ p := by
      rw [mul_inv_rev, Perm.mul_apply, hπl]
    rw [this]
    exact fp_le_mul_left π A σ (σ⁻¹ p)
  have step2 := h A'
  have step3 : PN A' = PN A := PN_image (Equiv.mulLeft π) A
  rw [e1] at step1
  rw [step3] at step2
  exact step1.trans step2

set_option maxHeartbeats 800000 in
lemma ineq53_of_last {N : ℕ}
    (h : ∀ A : Set (Perm (Fin (N + 1))),
      uniformAvg Finset.univ (fun σ => exp16 (fp A σ (Fin.last N))) ≤ (PN A)⁻¹) :
    Ineq53 (N + 1) := by
  intro A p
  set π : Perm (Fin (N + 1)) := swap p (Fin.last N) with hπ
  have hπp : π⁻¹ p = Fin.last N := by rw [hπ, swap_inv, swap_apply_left]
  set A' : Set (Perm (Fin (N + 1))) := (Equiv.mulRight π) '' A with hA'
  have e1 := uniformAvg_univ_equiv (Equiv.mulRight π) (fun σ => exp16 (fp A' σ (Fin.last N)))
  simp only [Equiv.coe_mulRight] at e1
  have step1 : uniformAvg Finset.univ (fun σ => exp16 (fp A σ p))
      ≤ uniformAvg Finset.univ (fun σ => exp16 (fp A' (σ * π) (Fin.last N))) := by
    apply uniformAvg_mono
    intro σ _
    apply exp16_mono
    rw [← hπp]
    exact fp_le_mul_right π A σ p
  have step2 := h A'
  have step3 : PN A' = PN A := PN_image (Equiv.mulRight π) A
  rw [e1] at step1
  rw [step3] at step2
  exact step1.trans step2

/-! ### The induction step -/

lemma fp_le_fpm {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (p c : Fin N) :
    fp A σ p ≤ fpm A σ p c := by
  unfold fp fpm
  exact le_iInf₂ fun s hs => iInf₂_le s hs.1

/-- `f(A,σ,i) ≤ f(A,σ,k,i)` for any `k`. -/
lemma fp_le_fpm' {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (i k : Fin N) :
    fp A σ i ≤ fpm A σ k i := by
  unfold fp fpm
  refine le_iInf₂ fun s hs => (iInf₂_le s hs.1).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [hs.2]
  nlinarith [sq_nonneg (s k)]

lemma exists_ne_of_one_le {N : ℕ} (hN : 1 ≤ N) (j : Fin (N + 1)) : ∃ k : Fin (N + 1), k ≠ j := by
  by_contra h
  push Not at h
  have e : (0 : Fin (N + 1)) = Fin.last N := (h 0).trans (h _).symm
  have := congrArg Fin.val e
  simp at this
  omega

lemma step54 {N : ℕ} (hN : 1 ≤ N) (ih53 : Ineq53 N) (A : Set (Perm (Fin (N + 1)))) :
    uniformAvg Finset.univ (fun σ => exp16 (fp A σ (σ⁻¹ (Fin.last N)))) ≤ (PN A)⁻¹ := by
  rw [uniformAvg_univ_G, PN_eq_sections]
  set a : Fin (N + 1) → ℝ≥0∞ := fun i => uniformProb (G N i) A with ha
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  by_cases hA : a j = 0
  · have hz : ∑ i, a i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm ((hj i (Finset.mem_univ i)).trans hA.le) zero_le
    rw [show ∑ i, uniformProb (G N i) A = ∑ i, a i from rfl, hz, mul_zero, ENNReal.inv_zero]
    exact le_top
  have hane : ∀ i, a i ≠ ⊤ := fun i => uniformProb_ne_top _ _
  set α : Fin (N + 1) → ℝ := fun i => (a i).toReal with hα
  set β : ℝ := α j with hβdef
  have hα' : ∀ i, a i = ENNReal.ofReal (α i) := fun i => (ENNReal.ofReal_toReal (hane i)).symm
  have hα0 : ∀ i, 0 ≤ α i := fun i => ENNReal.toReal_nonneg
  have hβ : 0 < β := by
    rw [hβdef, hα]
    exact ENNReal.toReal_pos hA (hane j)
  have hαβ : ∀ i, α i ≤ β := fun i => ENNReal.toReal_mono (hane j) (hj i (Finset.mem_univ i))
  have hbj : (a j)⁻¹ = ENNReal.ofReal ((2 - β / β) / β) := by
    rw [hα' j, ← hβdef, div_self hβ.ne', ← ENNReal.ofReal_inv_of_pos hβ]
    norm_num
  obtain ⟨k, hk⟩ := exists_ne_of_one_le hN j
  have hF : ∀ i, uniformAvg (G N i) (fun σ => exp16 (fp A σ (σ⁻¹ (Fin.last N))))
      ≤ ENNReal.ofReal ((2 - α i / β) / β) := by
    intro i
    have hcongr : uniformAvg (G N i) (fun σ => exp16 (fp A σ (σ⁻¹ (Fin.last N))))
        = uniformAvg (G N i) (fun σ => exp16 (fp A σ i)) := by
      apply uniformAvg_congr
      intro σ hσ
      have : σ i = Fin.last N := by simpa [G] using hσ
      rw [← this]
      simp
    rw [hcongr]
    by_cases hij : i = j
    · subst hij
      rw [← hbj]
      refine le_trans (uniformAvg_mono _ fun σ _ => exp16_mono (fp_le_fpm' A σ i k)) ?_
      exact cor_5_5_core ih53 A i k (Ne.symm hk)
    · refine section_bound (G N i) (fun σ => fp A σ i) (fun σ => g A σ i j) (fun σ => fpm A σ j i)
        (fun lam h0 h1 σ _ => lemma_5_3_core A i j hij σ lam h0 h1) (α i) β (hα0 i) (hαβ i) hβ ?_ ?_
      · rw [← hα' j]
        exact lemma_5_6_core (Or.inl ih53) A i j (Ne.symm hij)
      · rw [← hα' i]
        exact cor_5_5_core ih53 A i j hij
  have := combine_sections (ι := Fin (N + 1)) _ a α hα' hα0 β hβ hαβ hF
  rwa [Fintype.card_fin] at this

lemma step53 {N : ℕ} (hN : 1 ≤ N) (ih54 : Ineq54 N) (A : Set (Perm (Fin (N + 1)))) :
    uniformAvg Finset.univ (fun σ => exp16 (fp A σ (Fin.last N))) ≤ (PN A)⁻¹ := by
  rw [uniformAvg_univ_G', PN_eq_sections']
  set a : Fin (N + 1) → ℝ≥0∞ := fun i => uniformProb (G' N i) A with ha
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ a Finset.univ_nonempty
  by_cases hA : a j = 0
  · have hz : ∑ i, a i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm ((hj i (Finset.mem_univ i)).trans hA.le) zero_le
    rw [show ∑ i, uniformProb (G' N i) A = ∑ i, a i from rfl, hz, mul_zero, ENNReal.inv_zero]
    exact le_top
  have hane : ∀ i, a i ≠ ⊤ := fun i => uniformProb_ne_top _ _
  set α : Fin (N + 1) → ℝ := fun i => (a i).toReal with hα
  set β : ℝ := α j with hβdef
  have hα' : ∀ i, a i = ENNReal.ofReal (α i) := fun i => (ENNReal.ofReal_toReal (hane i)).symm
  have hα0 : ∀ i, 0 ≤ α i := fun i => ENNReal.toReal_nonneg
  have hβ : 0 < β := by
    rw [hβdef, hα]
    exact ENNReal.toReal_pos hA (hane j)
  have hαβ : ∀ i, α i ≤ β := fun i => ENNReal.toReal_mono (hane j) (hj i (Finset.mem_univ i))
  have hbj : (a j)⁻¹ = ENNReal.ofReal ((2 - β / β) / β) := by
    rw [hα' j, ← hβdef, div_self hβ.ne', ← ENNReal.ofReal_inv_of_pos hβ]
    norm_num
  obtain ⟨k, hk⟩ := exists_ne_of_one_le hN j
  have hF : ∀ i, uniformAvg (G' N i) (fun σ => exp16 (fp A σ (Fin.last N)))
      ≤ ENNReal.ofReal ((2 - α i / β) / β) := by
    intro i
    by_cases hij : i = j
    · subst hij
      rw [← hbj]
      refine le_trans (uniformAvg_mono _ fun σ _ =>
        exp16_mono (fp_le_fpm' A σ (Fin.last N) (σ⁻¹ k))) ?_
      exact cor_5_9_core ih54 A i k hk
    · refine section_bound (G' N i) (fun σ => fp A σ (Fin.last N))
        (fun σ => g A σ (Fin.last N) (σ⁻¹ j)) (fun σ => fpm A σ (σ⁻¹ j) (Fin.last N))
        (fun lam h0 h1 σ hσ => lemma_5_7_core A σ j (by
          have : σ (Fin.last N) = i := by simpa [G'] using hσ
          rw [this]; exact Ne.symm hij) lam h0 h1) (α i) β (hα0 i) (hαβ i) hβ ?_ ?_
      · rw [← hα' j]
        exact lemma_5_10_core (Or.inr ih54) A i j hij
      · rw [← hα' i]
        exact cor_5_9_core ih54 A i j (Ne.symm hij)
  have := combine_sections (ι := Fin (N + 1)) _ a α hα' hα0 β hβ hαβ hF
  rwa [Fintype.card_fin] at this

/-! ### Small cases and the induction -/

lemma perm_eq_of_le_one {N : ℕ} (hN : N ≤ 1) (σ τ : Perm (Fin N)) : σ = τ := by
  ext ℓ
  have := (σ ℓ).isLt
  have := (τ ℓ).isLt
  omega

lemma f_eq_zero_of_mem {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (hσ : σ ∈ A) :
    f A σ = 0 := by
  apply le_antisymm _ zero_le
  unfold f
  have h0 : (fun _ : Fin N => (0 : ℝ)) ∈ V A σ :=
    subset_convexHull ℝ _ ⟨fun ℓ => Or.inl rfl, σ, hσ, fun _ _ => rfl⟩
  refine (iInf₂_le _ h0).trans ?_
  simp

lemma fp_eq_zero_of_mem {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (hσ : σ ∈ A)
    (p : Fin N) : fp A σ p = 0 := by
  apply le_antisymm _ zero_le
  unfold fp
  have h0 : (fun _ : Fin N => (0 : ℝ)) ∈ V A σ :=
    subset_convexHull ℝ _ ⟨fun ℓ => Or.inl rfl, σ, hσ, fun _ _ => rfl⟩
  refine (iInf₂_le _ h0).trans ?_
  simp

lemma ineq_small {N : ℕ} (hN : N ≤ 1) (A : Set (Perm (Fin N))) (F : Perm (Fin N) → ℝ≥0∞)
    (hF : ∀ σ ∈ A, F σ ≤ 1) : uniformAvg Finset.univ F ≤ (PN A)⁻¹ := by
  rcases A.eq_empty_or_nonempty with hA | ⟨τ, hτ⟩
  · subst hA
    have : PN (∅ : Set (Perm (Fin N))) = 0 := by
      unfold PN uniformProb; simp
    rw [this, ENNReal.inv_zero]
    exact le_top
  · have hall : ∀ σ, F σ = F τ := fun σ => by rw [perm_eq_of_le_one hN σ τ]
    have : uniformAvg Finset.univ F = F τ := by
      unfold uniformAvg
      rw [Finset.sum_congr rfl fun σ _ => hall σ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← mul_assoc, ENNReal.inv_mul_cancel (by simp [Fintype.card_ne_zero]) (ENNReal.natCast_ne_top _),
        one_mul]
    rw [this]
    refine (hF τ hτ).trans ?_
    rw [ENNReal.one_le_inv]
    exact uniformProb_le_one _ _

theorem ineq_all (N : ℕ) : Ineq53 N ∧ Ineq54 N := by
  induction N with
  | zero => exact ⟨fun A p => p.elim0, fun A p => p.elim0⟩
  | succ N ih =>
    cases N with
    | zero =>
      refine ⟨fun A p => ?_, fun A p => ?_⟩
      · apply ineq_small (by norm_num) A
        intro σ hσ
        rw [fp_eq_zero_of_mem A σ hσ, exp16_zero]
      · apply ineq_small (by norm_num) A
        intro σ hσ
        rw [fp_eq_zero_of_mem A σ hσ, exp16_zero]
    | succ M =>
      exact ⟨ineq53_of_last (step53 (by omega) ih.2), ineq54_of_last (step54 (by omega) ih.1)⟩

/-- Proposition 5.2. -/
theorem prop_5_2_core {N : ℕ} (A : Set (Perm (Fin N))) (p : Fin N) :
    uniformAvg Finset.univ (fun σ => exp16 (fp A σ p)) ≤ (PN A)⁻¹ ∧
      uniformAvg Finset.univ (fun σ => exp16 (fp A σ (σ⁻¹ p))) ≤ (PN A)⁻¹ :=
  ⟨(ineq_all N).1 A p, (ineq_all N).2 A p⟩

lemma f_le_fp {N : ℕ} (A : Set (Perm (Fin N))) (σ : Perm (Fin N)) (p : Fin N) :
    f A σ ≤ fp A σ p := by
  unfold f fp
  refine le_iInf₂ fun s hs => (iInf₂_le s hs).trans ?_
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg (s p)]

/-- Theorem 5.1. -/
theorem theorem_5_1_core {N : ℕ} (A : Set (Perm (Fin N))) :
    uniformAvg Finset.univ (fun σ => exp16 (f A σ)) ≤ (PN A)⁻¹ := by
  cases N with
  | zero =>
    apply ineq_small (by norm_num) A
    intro σ hσ
    rw [f_eq_zero_of_mem A σ hσ, exp16_zero]
  | succ M =>
    refine le_trans (uniformAvg_mono _ fun σ _ => exp16_mono (f_le_fp A σ (Fin.last M))) ?_
    exact (ineq_all (M + 1)).1 A (Fin.last M)

end TalagrandConc.SymmetricGroup

open TalagrandConc.SymmetricGroup
open Equiv

theorem solution {N : ℕ} (A : Set (Perm (Fin N))) :
    uniformAvg Finset.univ (fun σ => exp16 (f A σ)) ≤ (PN A)⁻¹ := by
  exact theorem_5_1_core A
