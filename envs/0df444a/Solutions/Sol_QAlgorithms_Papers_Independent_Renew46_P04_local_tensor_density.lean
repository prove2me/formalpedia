-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P04.local_tensor_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T04:44:37.081622+00:00
-- url     : https://prove2.me/submissions/ccc0a276-2d5a-4313-ad81-02f2389e2a10

import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_projective_series
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_projective_crossnorm_ball
import Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P04_bilinear_extension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic

noncomputable section
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1000000

open QAlgorithms.Papers.Independent.Renew46.P04
open scoped BigOperators

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNorm
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorSeminormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.linearOperatorNormedSpace
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedGroup
attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P04.dualNormedSpace

namespace X9Local
variable {K X Y : Type*} [RCLike K]
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

noncomputable def algebraicPair : X →ₗ[K] Y →ₗ[K] Algebraic K X Y :=
  LinearMap.mk₂ K (fun x y => PiTensorProduct.tprod K (pair x y))
    (fun x x' y => by
      have e : ∀ x0 : X, pair x0 y = Function.update (pair 0 y) false (ULift.up x0) := by
        intro x0; funext b; cases b <;> rfl
      rw [e (x + x'), e x, e x']
      exact (PiTensorProduct.tprod K).map_update_add (pair 0 y) false (ULift.up x) (ULift.up x'))
    (fun c x y => by
      have e : ∀ x0 : X, pair x0 y = Function.update (pair 0 y) false (ULift.up x0) := by
        intro x0; funext b; cases b <;> rfl
      rw [e (c • x), e x]
      exact (PiTensorProduct.tprod K).map_update_smul (pair 0 y) false c (ULift.up x))
    (fun x y y' => by
      have e : ∀ y0 : Y, pair x y0 = Function.update (pair x 0) true (ULift.up y0) := by
        intro y0; funext b; cases b <;> rfl
      rw [e (y + y'), e y, e y']
      exact (PiTensorProduct.tprod K).map_update_add (pair x 0) true (ULift.up y) (ULift.up y'))
    (fun c x y => by
      have e : ∀ y0 : Y, pair x y0 = Function.update (pair x 0) true (ULift.up y0) := by
        intro y0; funext b; cases b <;> rfl
      rw [e (c • y), e y]
      exact (PiTensorProduct.tprod K).map_update_smul (pair x 0) true c (ULift.up y))


def purePair : X →ₗ[K] Y →ₗ[K] Projective K X Y :=
  LinearMap.mk₂ K (fun x y => pure (K := K) x y)
    (fun x x' y => by change algebraicInclusion (algebraicPair (x + x') y) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)
    (fun c x y => by change algebraicInclusion (algebraicPair (c • x) y) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)
    (fun x y y' => by change algebraicInclusion (algebraicPair x (y + y')) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)
    (fun c x y => by change algebraicInclusion (algebraicPair x (c • y)) = _; simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]; rfl)

lemma pure_eq (x : X) (y : Y) : pure (K := K) x y = purePair x y := rfl

lemma pure_norm (x : X) (y : Y) : ‖pure (K := K) x y‖ = ‖x‖ * ‖y‖ :=
  (projective_crossnorm_ball (K := K) (X := X) (Y := Y)).1 x y

lemma pure_dist (x a : X) (y b : Y) (ha : ‖a‖ = 1) (hy : ‖y‖ = 1) :
    ‖pure (K := K) x y - pure (K := K) a b‖ ≤ ‖x - a‖ + ‖y - b‖ := by
  have he : pure (K := K) x y - pure (K := K) a b = pure (K := K) (x - a) y + pure (K := K) a (y - b) := by
    simp only [pure_eq, map_sub, LinearMap.sub_apply]; abel
  rw [he]
  simpa only [pure_norm, ha, hy, mul_one, one_mul] using
    norm_add_le (pure (K := K) (x - a) y) (pure (K := K) a (y - b))

theorem normalize (x : X) (y : Y) (v0 : X) (w0 : Y) (hv0 : ‖v0‖ = 1) (hw0 : ‖w0‖ = 1) :
    ∃ (x' : X) (y' : Y), ‖x'‖ = 1 ∧ ‖y'‖ = 1 ∧
      ((‖x‖ * ‖y‖ : ℝ) : K) • pure (K := K) x' y' = pure (K := K) x y := by
  by_cases h : x = 0 ∨ y = 0
  · refine ⟨v0, w0, hv0, hw0, ?_⟩
    rcases h with h | h <;> simp [h, pure_eq]
  · push_neg at h
    obtain ⟨hx, hy⟩ := h
    have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    refine ⟨((‖x‖⁻¹ : ℝ) : K) • x, ((‖y‖⁻¹ : ℝ) : K) • y, ?_, ?_, ?_⟩
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 (norm_pos_iff.2 hx)), inv_mul_cancel₀ hnx]
    · rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 (norm_pos_iff.2 hy)), inv_mul_cancel₀ hny]
    · simp only [pure_eq, map_smul, LinearMap.smul_apply, smul_smul]
      rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul]
      have : ‖x‖ * ‖y‖ * (‖y‖⁻¹ * ‖x‖⁻¹) = 1 := by field_simp
      rw [this, RCLike.ofReal_one, one_smul]


lemma finite_rep {n : ℕ} (x : Fin n → X) (y : Fin n → Y) :
    (∑ i, ‖x i‖ * ‖y i‖) ∈ tensorCosts (∑ i, pure (K := K) (x i) (y i)) := by
  classical
  let xx : ℕ → X := Function.extend Fin.val x 0
  let yy : ℕ → Y := Function.extend Fin.val y 0
  have hx (i : Fin n) : xx i.val = x i := Fin.val_injective.extend_apply x 0 i
  have hy (i : Fin n) : yy i.val = y i := Fin.val_injective.extend_apply y 0 i
  have hz (k : ℕ) (hk : k ∉ Set.range (Fin.val : Fin n → ℕ)) : xx k = 0 ∧ yy k = 0 :=
    ⟨Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ hk⟩
  have hp : (fun k => pure (K := K) (xx k) (yy k)) =
      Function.extend Fin.val (fun i => pure (K := K) (x i) (y i)) 0 := by
    funext k
    by_cases hk : k ∈ Set.range (Fin.val : Fin n → ℕ)
    · obtain ⟨i, rfl⟩ := hk
      rw [hx, hy, Fin.val_injective.extend_apply]
    · simp [hz k hk, pure_eq, Function.extend_apply' _ _ _ hk]
  have hc : (fun k => ‖xx k‖ * ‖yy k‖) =
      Function.extend Fin.val (fun i => ‖x i‖ * ‖y i‖) 0 := by
    funext k
    by_cases hk : k ∈ Set.range (Fin.val : Fin n → ℕ)
    · obtain ⟨i, rfl⟩ := hk
      rw [hx, hy, Fin.val_injective.extend_apply]
    · simp [hz k hk, Function.extend_apply' _ _ _ hk]
  have hs : HasSum (fun k => ‖xx k‖ * ‖yy k‖) (∑ i, ‖x i‖ * ‖y i‖) := by
    rw [hc]; exact (hasSum_extend_zero Fin.val_injective).2 (hasSum_fintype _)
  refine ⟨xx, yy, ⟨?_, hs.summable, ?_⟩, hs.tsum_eq.symm⟩
  · refine ⟨(∑ i, ‖x i‖) + ∑ i, ‖y i‖, fun k => ?_⟩
    have hsx : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsy : 0 ≤ ∑ i, ‖y i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    by_cases hk : k ∈ Set.range (Fin.val : Fin n → ℕ)
    · obtain ⟨i, rfl⟩ := hk
      rw [hx, hy]
      have hxi : ‖x i‖ ≤ ∑ j, ‖x j‖ := Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      have hyi : ‖y i‖ ≤ ∑ j, ‖y j‖ := Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      constructor <;> linarith
    · simp only [(hz k hk).1, (hz k hk).2, norm_zero]
      constructor <;> linarith
  · rw [hp]; exact (hasSum_extend_zero Fin.val_injective).2 (hasSum_fintype _)

lemma zero_attains : TensorAttains (0 : Projective K X Y) := by
  have := finite_rep (K := K) (n := 0) (Fin.elim0 : Fin 0 → X) (Fin.elim0 : Fin 0 → Y)
  simpa [TensorAttains] using this

lemma unit_scalar_distance (c : K) (hc : ‖c‖ = 1) :
    ‖c - 1‖ ^ 2 = 2 * (1 - RCLike.re c) := by
  rw [← RCLike.normSq_eq_def', RCLike.normSq_sub]
  simp [RCLike.normSq_eq_def', hc]
  <;> ring

lemma improve_pair (h : LocalBilinear K X Y)
    (f : Projective K X Y →L[K] K) (hf : ‖f‖ = 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ (x : X) (y : Y), ‖x‖ = 1 → ‖y‖ = 1 →
      1 - d < RCLike.re (f (pure (K := K) x y)) →
      ∃ (a : X) (b : Y), ‖a‖ = 1 ∧ ‖b‖ = 1 ∧
        f (pure (K := K) a b) = 1 ∧ ‖pure (K := K) x y - pure (K := K) a b‖ ≤ 2 * t := by
  obtain ⟨I, hI, _⟩ := (bilinear_extension (K := K) (X := X) (Y := Y) (Z := K)).1
  let B := I.symm f
  have hB : ‖B‖ = 1 := (I.symm.norm_map f).trans hf
  have hBf (a : X) (b : Y) : B (pair a b) = f (pure (K := K) a b) := by
    rw [← (bilinear_extension (K := K) (X := X) (Y := Y) (Z := K)).2.1 B a b,
      ← hI B, I.apply_symm_apply]
  obtain ⟨eta, heta, hloc⟩ := h (t ^ 2 / 16) (by positivity) B hB
  let d := min eta (t ^ 2 / 8)
  have hd : 0 < d := lt_min heta (by positivity)
  refine ⟨d, hd, fun x y hx hy hg => ?_⟩
  have hn : 1 - eta < ‖B (pair x y)‖ := by
    rw [hBf]
    have := RCLike.re_le_norm (f (pure (K := K) x y))
    have := min_le_left eta (t ^ 2 / 8)
    dsimp [d] at hg
    linarith
  obtain ⟨a, b, ha, hb, hab, hxa, hyb⟩ := hloc x y hx hy hn
  have hxy : ‖pure (K := K) x y - pure (K := K) a b‖ ≤ t ^ 2 / 8 :=
    (pure_dist x a y b ha hy).trans (by linarith)
  let c := f (pure (K := K) a b)
  have hc : ‖c‖ = 1 := by simpa only [hBf] using hab
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  have hre : RCLike.re (f (pure (K := K) x y)) - RCLike.re c ≤ t ^ 2 / 8 := by
    calc
      _ = RCLike.re (f (pure (K := K) x y - pure (K := K) a b)) := by simp [c]
      _ ≤ ‖f (pure (K := K) x y - pure (K := K) a b)‖ := RCLike.re_le_norm _
      _ ≤ ‖f‖ * ‖pure (K := K) x y - pure (K := K) a b‖ := f.le_opNorm _
      _ ≤ t ^ 2 / 8 := by rw [hf, one_mul]; exact hxy
  have hphase : ‖c - 1‖ ≤ t := by
    have hsq := unit_scalar_distance c hc
    have hdt : d ≤ t ^ 2 / 8 := min_le_right _ _
    nlinarith only [hsq, hg, hre, hdt, ht, norm_nonneg (c - 1)]
  have hinv : ‖c⁻¹ - 1‖ ≤ t := by
    have he : c⁻¹ - 1 = c⁻¹ * (1 - c) := by field_simp
    rw [he, norm_mul, norm_inv, hc, inv_one, one_mul, norm_sub_rev]
    exact hphase
  refine ⟨c⁻¹ • a, b, ?_, hb, ?_, ?_⟩
  · rw [norm_smul, norm_inv, hc, inv_one, ha, one_mul]
  · simp only [pure_eq, map_smul, LinearMap.smul_apply]
    change c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc0
  · have hw : ‖pure (K := K) a b‖ = 1 := by rw [pure_norm, ha, hb, one_mul]
    have hdif : ‖pure (K := K) a b - pure (K := K) (c⁻¹ • a) b‖ ≤ t := by
      have he : pure (K := K) a b - pure (K := K) (c⁻¹ • a) b = (1 - c⁻¹) • pure (K := K) a b := by
        simp only [pure_eq, map_smul, LinearMap.smul_apply, sub_smul, one_smul]
      rw [he, norm_smul, hw, mul_one, norm_sub_rev]
      exact hinv
    calc
      ‖pure (K := K) x y - pure (K := K) (c⁻¹ • a) b‖ ≤
          ‖pure (K := K) x y - pure (K := K) a b‖ + ‖pure (K := K) a b - pure (K := K) (c⁻¹ • a) b‖ :=
        by simpa only [dist_eq_norm] using dist_triangle (pure (K := K) x y) (pure (K := K) a b) (pure (K := K) (c⁻¹ • a) b)
      _ ≤ t ^ 2 / 8 + t := add_le_add hxy hdif
      _ ≤ 2 * t := by nlinarith only [ht, mul_nonneg ht.le (sub_nonneg.mpr ht1)]

lemma approx_algebraic [Nontrivial X] [Nontrivial Y] (h : LocalBilinear K X Y)
    (u : Algebraic K X Y) (eps : ℝ) (heps : 0 < eps) :
    ∃ w : Projective K X Y, TensorAttains w ∧ ‖algebraicInclusion u - w‖ < eps := by
  classical
  let z : Projective K X Y := algebraicInclusion u
  by_cases hz : z = 0
  · refine ⟨0, zero_attains, ?_⟩
    change ‖z - 0‖ < eps
    simpa only [hz, sub_self, norm_zero] using heps
  obtain ⟨f, hf, hfz⟩ := exists_dual_vector K z (norm_ne_zero_iff.mpr hz)
  let M := ‖z‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let t := min 1 (eps / (8 * M))
  have ht : 0 < t := lt_min zero_lt_one (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hteps : 2 * t * M ≤ eps / 4 := by
    have := (le_div_iff₀ (show 0 < 8 * M by positivity)).mp (min_le_right 1 (eps / (8 * M)))
    dsimp [t]; nlinarith only [this]
  obtain ⟨d, hd, himprove⟩ := improve_pair h f hf t ht ht1
  let delta := min 1 (d * eps / 4)
  have hdelta : 0 < delta := lt_min zero_lt_one (by positivity)
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hde : delta ≤ d * eps / 4 := min_le_right _ _
  obtain ⟨hne, _, hinf⟩ := (projective_series (K := K) (X := X) (Y := Y)).2.1 u
  have hzu : ‖z‖ = ‖u‖ := (projective_series (K := K) (X := X) (Y := Y)).2.2.2.2.1 u
  obtain ⟨r, ⟨n, xx, yy, hu, hr⟩, hcost⟩ :=
    exists_lt_of_csInf_lt hne (show sInf (finiteCosts u) < ‖z‖ + delta by rw [← hinf, hzu]; linarith)
  obtain ⟨x0, hx0⟩ := exists_ne (0 : X)
  obtain ⟨y0, hy0⟩ := exists_ne (0 : Y)
  have hn := fun i => normalize (K := K) (xx i) (yy i)
    ((‖x0‖⁻¹ : K) • x0) ((‖y0‖⁻¹ : K) • y0)
    (norm_smul_inv_norm hx0) (norm_smul_inv_norm hy0)
  choose x y hx hy hxy using hn
  let a : Fin n → ℝ := fun i => ‖xx i‖ * ‖yy i‖
  have ha (i) : 0 ≤ a i := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hra : r = ∑ i, a i := hr
  have hza : z = ∑ i, (a i : K) • pure (K := K) (x i) (y i) := by
    simp only [a, hxy]
    change algebraicInclusion u = _
    rw [hu, map_sum]; rfl
  have hc : (∑ i, a i) < ‖z‖ + delta := by rwa [hra] at hcost
  have hrc : (∑ i, a i) ≤ M := by dsimp [M]; linarith
  let good : Fin n → Prop := fun i => 1 - d < RCLike.re (f (pure (K := K) (x i) (y i)))
  have heach (i : Fin n) : ∃ (v : X) (w : Y), ‖v‖ = 1 ∧ ‖w‖ = 1 ∧
      (good i → f (pure (K := K) v w) = 1 ∧ ‖pure (K := K) (x i) (y i) - pure (K := K) v w‖ ≤ 2 * t) := by
    by_cases hi : good i
    · obtain ⟨v, w, hv, hw, hfw, hdist⟩ := himprove (x i) (y i) (hx i) (hy i) hi
      exact ⟨v, w, hv, hw, fun _ => ⟨hfw, hdist⟩⟩
    · exact ⟨x i, y i, hx i, hy i, fun hi' => (hi hi').elim⟩
  choose v w hv hw hvw using heach
  let b : Fin n → ℝ := fun i => if good i then a i else 0
  have hb (i) : 0 ≤ b i := by dsimp [b]; split_ifs <;> positivity
  have hb_le (i) : b i ≤ a i := by dsimp [b]; split_ifs <;> simp [ha]
  let zz : Projective K X Y := ∑ i, (b i : K) • pure (K := K) (v i) (w i)
  have hnw (i) : ‖pure (K := K) (v i) (w i)‖ = 1 := by rw [pure_norm, hv, hw, one_mul]
  have hnp (i) : ‖pure (K := K) (x i) (y i)‖ = 1 := by rw [pure_norm, hx, hy, one_mul]
  have hvalue (i) : f ((b i : K) • pure (K := K) (v i) (w i)) = (b i : K) := by
    by_cases hi : good i
    · simp [map_smul, (hvw i hi).1]
    · simp [b, hi]
  have hfsum : f zz = ((∑ i, b i : ℝ) : K) := by
    simp only [zz, map_sum, hvalue, RCLike.ofReal_sum]
  have hbs : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => hb i
  have hnzz : ‖zz‖ = ∑ i, b i := by
    apply le_antisymm
    · calc
        ‖zz‖ ≤ ∑ i, ‖(b i : K) • pure (K := K) (v i) (w i)‖ := norm_sum_le _ _
        _ = ∑ i, b i := by simp [norm_smul, hnw, RCLike.norm_ofReal, abs_of_nonneg, hb]
    · have hle := f.le_opNorm zz
      rw [hf, one_mul, hfsum, RCLike.norm_ofReal, abs_of_nonneg hbs] at hle
      exact hle
  have hat : TensorAttains zz := by
    have hrep := finite_rep (K := K) (fun i => (b i : K) • v i) w
    have hnorms : (∑ i, ‖(b i : K) • v i‖ * ‖w i‖) = ∑ i, b i := by
      simp [norm_smul, hv, hw, RCLike.norm_ofReal, abs_of_nonneg, hb]
    have hterms : (∑ i, pure (K := K) ((b i : K) • v i) (w i)) = zz := by
      simp only [pure_eq, map_smul, LinearMap.smul_apply, zz]
    rw [hterms, hnorms, ← hnzz] at hrep
    exact hrep
  have hreal : (∑ i, a i * RCLike.re (f (pure (K := K) (x i) (y i)))) = ‖z‖ := by
    calc
      _ = RCLike.re (f (∑ i, (a i : K) • pure (K := K) (x i) (y i))) := by
        simp [map_sum, map_smul, RCLike.mul_re]
      _ = RCLike.re (f z) := by rw [← hza]
      _ = ‖z‖ := by rw [hfz, RCLike.ofReal_re]
  have hrei (i) : RCLike.re (f (pure (K := K) (x i) (y i))) ≤ 1 := by
    calc
      _ ≤ ‖f (pure (K := K) (x i) (y i))‖ := RCLike.re_le_norm _
      _ ≤ ‖f‖ * ‖pure (K := K) (x i) (y i)‖ := f.le_opNorm _
      _ = 1 := by rw [hf, hnp, one_mul]
  let badmass : ℝ := ∑ i, (a i - b i)
  have hbad : d * badmass < d * eps / 4 := by
    calc
      d * badmass = ∑ i, d * (a i - b i) := by rw [Finset.mul_sum]
      _ ≤ ∑ i, a i * (1 - RCLike.re (f (pure (K := K) (x i) (y i)))) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : good i
        · simp only [b, if_pos hi, sub_self, mul_zero]
          exact mul_nonneg (ha i) (sub_nonneg.mpr (hrei i))
        · have hri : RCLike.re (f (pure (K := K) (x i) (y i))) ≤ 1 - d := le_of_not_gt hi
          simp only [b, if_neg hi, sub_zero]
          nlinarith only [mul_le_mul_of_nonneg_left hri (ha i)]
      _ = (∑ i, a i) - ‖z‖ := by simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hreal]
      _ < delta := by linarith
      _ ≤ d * eps / 4 := hde
  have hbad' : badmass < eps / 4 := by nlinarith only [hbad, hd]
  refine ⟨zz, hat, ?_⟩
  have hdiff (i) : ‖(a i : K) • pure (K := K) (x i) (y i) - (b i : K) • pure (K := K) (v i) (w i)‖ ≤
      2 * t * a i + (a i - b i) := by
    by_cases hi : good i
    · simp only [b, if_pos hi, sub_self, add_zero, ← smul_sub, norm_smul,
        RCLike.norm_ofReal, abs_of_nonneg (ha i)]
      nlinarith only [mul_le_mul_of_nonneg_left (hvw i hi).2 (ha i)]
    · simp only [b, if_neg hi, RCLike.ofReal_zero, zero_smul, sub_zero, norm_smul,
        hnp, mul_one, RCLike.norm_ofReal, abs_of_nonneg (ha i)]
      nlinarith only [mul_nonneg ht.le (ha i)]
  calc
    ‖algebraicInclusion u - zz‖ =
        ‖∑ i, ((a i : K) • pure (K := K) (x i) (y i) - (b i : K) • pure (K := K) (v i) (w i))‖ := by
      rw [Finset.sum_sub_distrib, ← hza]
    _ ≤ ∑ i, ‖(a i : K) • pure (K := K) (x i) (y i) - (b i : K) • pure (K := K) (v i) (w i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, (2 * t * a i + (a i - b i)) := Finset.sum_le_sum fun i _ => hdiff i
    _ = 2 * t * (∑ i, a i) + badmass := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * t * M + badmass := by
      simpa only [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left hrc (show 0 ≤ 2 * t by positivity)) badmass
    _ < eps := by linarith

end X9Local

namespace X9Local
variable {K X Y : Type*} [RCLike K]
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

lemma cost_lower (z : Projective K X Y) {r : ℝ} (hr : r ∈ tensorCosts z) : ‖z‖ ≤ r := by
  obtain ⟨_, hb, hinf, _⟩ := (projective_series (K := K) (X := X) (Y := Y)).2.2.2.2.2.1 z
  rw [hinf]
  exact csInf_le hb hr

lemma zero_of_subsingleton_left [Subsingleton X] (z : Projective K X Y) : z = 0 := by
  obtain ⟨r, hr⟩ := ((projective_series (K := K) (X := X) (Y := Y)).2.2.2.2.2.1 z).1
  have hle := cost_lower z hr
  obtain ⟨x, y, _, hr⟩ := hr
  have hx : x = fun _ => 0 := funext fun i => Subsingleton.elim _ _
  have hr0 : r = 0 := by simpa [hx] using hr
  exact norm_eq_zero.mp (le_antisymm (hr0 ▸ hle) (norm_nonneg _))

lemma zero_of_subsingleton_right [Subsingleton Y] (z : Projective K X Y) : z = 0 := by
  obtain ⟨r, hr⟩ := ((projective_series (K := K) (X := X) (Y := Y)).2.2.2.2.2.1 z).1
  have hle := cost_lower z hr
  obtain ⟨x, y, _, hr⟩ := hr
  have hy : y = fun _ => 0 := funext fun i => Subsingleton.elim _ _
  have hr0 : r = 0 := by simpa [hy] using hr
  exact norm_eq_zero.mp (le_antisymm (hr0 ▸ hle) (norm_nonneg _))

end X9Local

variable {K : Type*} [RCLike K]
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

theorem solution (h : LocalBilinear K X Y) : TensorDense K X Y := by
  classical
  apply Metric.dense_iff.2
  intro z eps heps
  by_cases hX : Nontrivial X
  · letI := hX
    by_cases hY : Nontrivial Y
    · letI := hY
      have hdense := (projective_series (K := K) (X := X) (Y := Y)).2.2.2.1
      obtain ⟨u, hu⟩ := hdense.exists_dist_lt z (half_pos heps)
      obtain ⟨w, hw, hdist⟩ := X9Local.approx_algebraic h u (eps / 2) (half_pos heps)
      refine ⟨w, ?_, hw⟩
      change dist w z < eps
      rw [dist_comm w z]
      calc
        dist z w ≤ dist z (algebraicInclusion u) + dist (algebraicInclusion u) w := dist_triangle _ _ _
        _ < eps / 2 + eps / 2 := add_lt_add (by simpa [dist_comm] using hu) (by simpa [dist_eq_norm] using hdist)
        _ = eps := by ring
    · haveI : Subsingleton Y := not_nontrivial_iff_subsingleton.mp hY
      refine ⟨0, ?_, X9Local.zero_attains⟩
      simpa [X9Local.zero_of_subsingleton_right z] using heps
  · haveI : Subsingleton X := not_nontrivial_iff_subsingleton.mp hX
    refine ⟨0, ?_, X9Local.zero_attains⟩
    simpa [X9Local.zero_of_subsingleton_left z] using heps
