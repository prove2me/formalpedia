-- Prove2me | solution 1 for SaturatedNet.Uniqueness.proposition_2_i_ii
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T10:09:38.636748+00:00
-- url     : https://prove2.me/submissions/d0e50d78-4849-4c90-b645-4c0927732e19

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
import Theorems.Thm_BellmanDP_Markovian_perron_eigen_exists_unique


open Matrix Filter Topology
open scoped Matrix.Norms.Operator ENNReal NNReal

namespace SaturatedNet.Uniqueness.PerronProof

lemma spectrum_norm_le_weight {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (v : n → ℝ) (hv : ∀ i, 0 < v i) (r : ℝ)
    (hPv : P *ᵥ v ≤ r • v)
    (μ : ℂ) (hμ : μ ∈ spectrum ℂ (P.map (algebraMap ℝ ℂ))) : ‖μ‖ ≤ r := by
  classical
  let A := P.map (algebraMap ℝ ℂ)
  have heigen : Module.End.HasEigenvalue A.toLin' μ :=
    Module.End.HasEigenvalue.of_mem_spectrum (by rwa [Matrix.spectrum_toLin'])
  obtain ⟨z, hz⟩ := heigen.exists_hasEigenvector
  have heq : A *ᵥ z = μ • z := hz.apply_eq_smul
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz.2
  have hzj : 0 < ‖z j‖ := norm_pos_iff.mpr hj
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => ‖z i‖ / v i) ⟨j, Finset.mem_univ _⟩
  let a := ‖z i‖ / v i
  have ha : 0 < a := (div_pos hzj (hv j)).trans_le (hmax j (Finset.mem_univ j))
  have hbound : ∀ j, ‖z j‖ ≤ a * v j := fun j =>
    (div_le_iff₀ (hv j)).mp (hmax j (Finset.mem_univ j))
  have heqi : ‖z i‖ = a * v i := (div_mul_cancel₀ _ (hv i).ne').symm
  have hi : ∑ j, (P i j : ℂ) * z j = μ * z i := congrFun heq i
  have hrow : ‖μ‖ * ‖z i‖ ≤ a * (P *ᵥ v) i := by
    calc
      ‖μ‖ * ‖z i‖ = ‖∑ j, (P i j : ℂ) * z j‖ := by rw [hi, norm_mul]
      _ ≤ ∑ j, ‖(P i j : ℂ) * z j‖ := norm_sum_le _ _
      _ = ∑ j, P i j * ‖z j‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hP i _)]
      _ ≤ ∑ j, P i j * (a * v j) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbound j) (hP i j)
      _ = a * (P *ᵥ v) i := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hh := hrow.trans (mul_le_mul_of_nonneg_left (hPv i) ha.le)
  change ‖μ‖ * ‖z i‖ ≤ a * (r * v i) at hh
  rw [heqi] at hh
  nlinarith [mul_pos ha (hv i)]

lemma radius_le_weight {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (v : n → ℝ) (hv : ∀ i, 0 < v i) (r : ℝ)
    (hPv : P *ᵥ v ≤ r • v) : specRad P ≤ ENNReal.ofReal r := by
  unfold specRad spectralRadius
  refine iSup₂_le fun μ hμ => ?_
  simpa only [ofReal_norm, enorm_eq_nnnorm] using
    ENNReal.ofReal_le_ofReal (spectrum_norm_le_weight P hP v hv r hPv μ hμ)

lemma radius_ne_top {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) : specRad P ≠ ⊤ := by
  let A := P.map (algebraMap ℝ ℂ)
  have hb : specRad P ≤ ENNReal.ofReal (‖A‖ * ‖(1 : Matrix n n ℂ)‖) := by
    unfold specRad spectralRadius
    refine iSup₂_le fun μ hμ => ?_
    simpa only [ofReal_norm, enorm_eq_nnnorm] using
      ENNReal.ofReal_le_ofReal (spectrum.norm_le_norm_mul_of_mem hμ)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb

lemma eigenvalue_le_radius {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (v : n → ℝ) (hv : v ≠ 0) (r : ℝ) (hr : 0 ≤ r)
    (hPv : P *ᵥ v = r • v) : ENNReal.ofReal r ≤ specRad P := by
  let A := P.map (algebraMap ℝ ℂ)
  let z : n → ℂ := fun i => (v i : ℂ)
  have hz : z ≠ 0 := by
    intro h
    apply hv
    funext i
    have hi : (v i : ℂ) = 0 := congrFun h i
    exact_mod_cast hi
  have heq : A *ᵥ z = (r : ℂ) • z := by
    funext i
    have hi := congrFun hPv i
    change (∑ j, (P i j : ℂ) * (v j : ℂ)) = (r : ℂ) * (v i : ℂ)
    exact_mod_cast hi
  have heigen : Module.End.HasEigenvector A.toLin' (r : ℂ) z := ⟨Module.End.mem_genEigenspace_one.mpr heq, hz⟩
  have hm : (r : ℂ) ∈ spectrum ℂ A := by
    rw [← Matrix.spectrum_toLin']
    exact (Module.End.hasEigenvalue_of_hasEigenvector heigen).mem_spectrum
  have hb := le_iSup₂ (f := fun μ (_ : μ ∈ spectrum ℂ A) => (‖μ‖₊ : ℝ≥0∞)) (r : ℂ) hm
  simpa only [specRad, spectralRadius, A, Complex.nnnorm_real, Real.nnnorm_of_nonneg hr,
    ENNReal.ofReal_eq_coe_nnreal hr] using hb

lemma radius_transpose {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) : specRad Pᵀ = specRad P := by
  have hs : spectrum ℂ (Pᵀ.map (algebraMap ℝ ℂ)) =
      spectrum ℂ (P.map (algebraMap ℝ ℂ)) := by
    ext μ
    simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.transpose_map,
      Matrix.charpoly_transpose]
  unfold specRad spectralRadius
  rw [hs]

lemma radius_eq_of_positive_eigenvector {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (v : n → ℝ) (hv : ∀ i, 0 < v i) (r : ℝ) (hr : 0 ≤ r)
    (hPv : P *ᵥ v = r • v) : specRad P = ENNReal.ofReal r := by
  apply le_antisymm (radius_le_weight P hP v hv r hPv.le)
  apply eigenvalue_le_radius P v _ r hr hPv
  intro h
  have := hv (Classical.arbitrary n)
  rw [h] at this
  exact lt_irrefl _ this

end SaturatedNet.Uniqueness.PerronProof


open Matrix
open scoped Matrix.Norms.Operator ENNReal NNReal

namespace SaturatedNet.Uniqueness.PerronProof

lemma positive_eigenpair {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 < P i j) :
    ∃ (r : ℝ) (v : n → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ P *ᵥ v = r • v := by
  classical
  let e := (Fintype.equivFin n).symm
  let a : (i : Fin (Fintype.card n)) → Unit → Fin (Fintype.card n) → ℝ :=
    fun i _ j => P (e i) (e j)
  let m : ℝ := ∑ i, ∑ j, P (e i) (e j)
  have hm : ∀ i j, P (e i) (e j) ≤ m := by
    intro i j
    apply le_trans (Finset.single_le_sum (fun k _ => (hP (e i) (e k)).le) (Finset.mem_univ j))
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => (hP (e k) (e l)).le))
      (Finset.mem_univ i)
  have h : BellmanDP.Markovian.MarkovHyp a (fun _ => Set.univ) m := by
    constructor
    · intro y i
      exact ⟨(), Set.mem_univ _, fun _ _ => le_rfl⟩
    · intro i q _ j
      exact hP (e i) (e j)
    · intro i q _ j
      exact hm i j
    · refine ⟨fun _ => (), by simp, ?_⟩
      intro q _
      exact le_rfl
  obtain ⟨r, y, hr, hy, heq, _, _⟩ :=
    BellmanDP.Markovian.perron_eigen_exists_unique Fintype.card_pos a (fun _ => Set.univ) m h
  refine ⟨r, fun i => y (e.symm i), hr, fun i => hy _, ?_⟩
  funext i
  obtain ⟨q, _, hq⟩ := (heq (e.symm i)).1
  change (∑ j, P i j * y (e.symm j)) = r * y (e.symm i)
  calc
    _ = ∑ j, P i (e j) * y j := by simpa using (e.sum_comp (fun j => P i j * y (e.symm j))).symm
    _ = r * y (e.symm i) := by simpa only [a, e.apply_symm_apply] using hq

lemma normalized_positive_eigenpair {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 < P i j) :
    ∃ (r : ℝ) (v : n → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧
      (∑ i, v i) = 1 ∧ P *ᵥ v = r • v ∧ specRad P = ENNReal.ofReal r := by
  classical
  obtain ⟨r, v, hr, hv, heq⟩ := positive_eigenpair P hP
  let s := ∑ i, v i
  have hs : 0 < s := Finset.sum_pos (fun i _ => hv i) Finset.univ_nonempty
  let w : n → ℝ := fun i => v i / s
  have hw : ∀ i, 0 < w i := fun i => div_pos (hv i) hs
  have hsum : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self hs.ne'
  have heqw : P *ᵥ w = r • w := by
    funext i
    change (∑ j, P i j * (v j / s)) = r * (v i / s)
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    exact congrArg (fun t : ℝ => t/s) (congrFun heq i)
  exact ⟨r, w, hr, hw, hsum, heqw,
    radius_eq_of_positive_eigenvector P (fun i j => (hP i j).le) w hw r hr.le heqw⟩

end SaturatedNet.Uniqueness.PerronProof


open Matrix Filter Topology
open scoped Matrix.Norms.Operator ENNReal NNReal

namespace SaturatedNet.Uniqueness.PerronProof

lemma sum_bound {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (r : ℝ) (v : n → ℝ) (hv : 0 ≤ v) (hs : ∑ i, v i = 1)
    (heq : P *ᵥ v = r • v) : r ≤ ∑ i, ∑ j, P i j := by
  have hv1 : ∀ i, v i ≤ 1 := fun i => hs ▸
    Finset.single_le_sum (fun j _ => hv j) (Finset.mem_univ i)
  calc
    r = ∑ i, r * v i := by rw [← Finset.mul_sum, hs, mul_one]
    _ = ∑ i, ∑ j, P i j * v j := by
      apply Finset.sum_congr rfl
      intro i _
      exact (congrFun heq i).symm
    _ ≤ ∑ i, ∑ j, P i j := Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (hP i j) (hv1 j)

lemma right_and_blocks {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    (∃ v : n → ℝ, 0 ≤ v ∧ v ≠ 0 ∧ P *ᵥ v = (specRad P).toReal • v) ∧
      (∀ S : Finset n, specRad (block P S) ≤ specRad P) := by
  classical
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  let A : ℕ → Matrix n n ℝ := fun k i j => P i j + ε k
  have hε : ∀ k, 0 < ε k := fun k => by dsimp [ε]; positivity
  have hε1 : ∀ k, ε k ≤ 1 := fun k => by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  have hA : ∀ k i j, 0 < A k i j := fun k i j => add_pos_of_nonneg_of_pos (hP i j) (hε k)
  choose r v hr hv hs heq hrad using fun k => normalized_positive_eigenpair (A k) (hA k)
  let C : ℝ := ∑ i, ∑ j, (P i j + 1)
  have hbound : ∀ k, r k ≤ C := by
    intro k
    apply (sum_bound (A k) (fun i j => (hA k i j).le) (r k) (v k)
      (fun i => (hv k i).le) (hs k) (heq k)).trans
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      add_le_add le_rfl (hε1 k)
  have hv1 : ∀ k i, v k i ≤ 1 := fun k i => (hs k) ▸
    Finset.single_le_sum (fun j _ => (hv k j).le) (Finset.mem_univ i)
  have hcompact : IsCompact (Set.Icc (0 : ℝ) C ×ˢ Set.Icc (0 : n → ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (x := fun k => (r k, v k)) (fun k => ⟨⟨(hr k).le, hbound k⟩,
      ⟨fun i => (hv k i).le, hv1 k⟩⟩)
  have hrlim : Tendsto (fun k => r (φ k)) atTop (𝓝 a.1) := (continuous_fst.tendsto a).comp hlim
  have hvlim : ∀ i, Tendsto (fun k => v (φ k) i) atTop (𝓝 (a.2 i)) :=
    tendsto_pi_nhds.mp ((continuous_snd.tendsto a).comp hlim)
  have hεlim : Tendsto (fun k => ε (φ k)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hsum : ∑ i, a.2 i = 1 := by
    have ht := tendsto_finsetSum Finset.univ (fun i _ => hvlim i)
    have ht' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (∑ i, a.2 i)) := by
      simpa only [hs] using ht
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  have hae : P *ᵥ a.2 = a.1 • a.2 := by
    funext i
    have ht : Tendsto (fun k => ∑ j, A (φ k) i j * v (φ k) j) atTop
        (𝓝 (∑ j, P i j * a.2 j)) := by
      apply tendsto_finsetSum
      intro j _
      simpa only [add_zero] using (tendsto_const_nhds.add hεlim).mul (hvlim j)
    have ht' : Tendsto (fun k => ∑ j, A (φ k) i j * v (φ k) j) atTop
        (𝓝 (a.1 * a.2 i)) := by
      have hh := hrlim.mul (hvlim i)
      convert hh using 1
      funext k
      exact congrFun (heq (φ k)) i
    exact tendsto_nhds_unique ht ht'
  have hane : a.2 ≠ 0 := by
    intro h
    simp [h] at hsum
  have hle : ∀ k, specRad P ≤ ENNReal.ofReal (r k) := by
    intro k
    apply radius_le_weight P hP (v k) (hv k) (r k)
    intro i
    calc
      (P *ᵥ v k) i ≤ (A k *ᵥ v k) i := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hε k).le) (hv k j).le
      _ = (r k • v k) i := congrFun (heq k) i
  have hrho : (specRad P).toReal ≤ a.1 := by
    apply ge_of_tendsto' hrlim
    intro k
    rw [← ENNReal.ofReal_le_ofReal_iff (hr (φ k)).le, ENNReal.ofReal_toReal (radius_ne_top P)]
    exact hle (φ k)
  have hreverse := eigenvalue_le_radius P a.2 hane a.1 ha.1.1 hae
  have hra : a.1 = (specRad P).toReal := by
    apply le_antisymm _ hrho
    rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (radius_ne_top P)]
    exact hreverse
  refine ⟨⟨a.2, ha.2.1, hane, by rwa [← hra]⟩, ?_⟩
  intro S
  have hblock : ∀ k, specRad (block P S) ≤ ENNReal.ofReal (r k) := by
    intro k
    apply radius_le_weight (block P S) (fun i j => hP i j)
      (fun i => v k i) (fun i => hv k i) (r k)
    intro i
    calc
      (block P S *ᵥ (fun j : S => v k j)) i = ∑ j ∈ S, P i j * v k j := by
        exact (Finset.sum_subtype S (fun _ => Iff.rfl) (fun j => P i j * v k j)).symm
      _ ≤ ∑ j, P i j * v k j := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun j _ _ => mul_nonneg (hP i j) (hv k j).le)
      _ ≤ (A k *ᵥ v k) i := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hε k).le) (hv k j).le
      _ = (r k • (fun j : S => v k j)) i := congrFun (heq k) i
  have hb : (specRad (block P S)).toReal ≤ a.1 := by
    apply ge_of_tendsto' hrlim
    intro k
    rw [← ENNReal.ofReal_le_ofReal_iff (hr (φ k)).le,
      ENNReal.ofReal_toReal (radius_ne_top (block P S))]
    exact hblock (φ k)
  rw [hra] at hb
  exact (ENNReal.toReal_le_toReal (radius_ne_top _) (radius_ne_top _)).mp hb

end SaturatedNet.Uniqueness.PerronProof


open Matrix
open SaturatedNet.Uniqueness.PerronProof

namespace SaturatedNet.Uniqueness

theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) :
    (Nonempty n → ∃ p π : n → ℝ, 0 ≤ p ∧ p ≠ 0 ∧ 0 ≤ π ∧ π ≠ 0 ∧
      P *ᵥ p = (specRad P).toReal • p ∧ π ᵥ* P = (specRad P).toReal • π) ∧
    (∀ S : Finset n, specRad (block P S) ≤ specRad P) := by
  classical
  constructor
  · intro hn
    let : Nonempty n := hn
    obtain ⟨⟨p, hp0, hp, heq⟩, _⟩ := right_and_blocks P hP
    obtain ⟨⟨π, hπ0, hπ, heqπ⟩, _⟩ := right_and_blocks Pᵀ (fun i j => hP j i)
    refine ⟨p, π, hp0, hp, hπ0, hπ, heq, ?_⟩
    simpa only [Matrix.mulVec_transpose, radius_transpose] using heqπ
  · intro S
    cases isEmpty_or_nonempty n with
    | inl hn =>
      let : IsEmpty n := hn
      simp [specRad, spectralRadius, spectrum.of_subsingleton]
    | inr hn =>
      let : Nonempty n := hn
      exact (right_and_blocks P hP).2 S

end SaturatedNet.Uniqueness
