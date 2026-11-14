-- Prove2me | solution 1 for TensorNP.SpectralNorm.Tl_max_singular_value
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T05:18:41.926662+00:00
-- url     : https://prove2.me/submissions/096fc096-a168-4c04-9958-5a582cb341c4

import Definitions.Def_TensorNP_SpectralNorm_Tensor
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_TensorNP_SpectralNorm_CliqueTensor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp


open scoped BigOperators
open TensorNP.SpectralNorm Finset

namespace TensorSpectralCommon

lemma raw_l2norm_eq_norm {n : ℕ} (x : Fin n → ℝ) :
    l2norm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  simpa [l2norm] using (EuclideanSpace.norm_eq (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))).symm

lemma raw_l2norm_zero {n : ℕ} : l2norm (0 : Fin n → ℝ) = 0 := by
  simp [l2norm]

lemma raw_l2norm_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) : l2norm x ≠ 0 := by
  simpa only [raw_l2norm_eq_norm, norm_ne_zero_iff, ne_eq, WithLp.toLp_eq_zero] using hx

lemma raw_l2norm_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) :
    l2norm (c • x) = |c| * l2norm x := by
  simp only [l2norm, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma raw_trilinear_smul1 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (c : ℝ) (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) :
    trilinear A (c • x) y z = c * trilinear A x y z := by
  simp only [trilinear, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_comm, mul_left_comm]

lemma raw_trilinear_smul2 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (c : ℝ) (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) :
    trilinear A x (c • y) z = c * trilinear A x y z := by
  simp only [trilinear, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]

lemma raw_trilinear_smul3 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (c : ℝ) (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) :
    trilinear A x y (c • z) = c * trilinear A x y z := by
  simp only [trilinear, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]


lemma raw_l2norm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ l2norm x := Real.sqrt_nonneg _

lemma raw_ne_zero_of_unit {n : ℕ} (x : Fin n → ℝ) (hx : l2norm x = 1) : x ≠ 0 := by
  exact fun h => by simp [h, raw_l2norm_zero] at hx

lemma raw_normalized_unit {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    l2norm ((l2norm x)⁻¹ • x) = 1 := by
  rw [raw_l2norm_smul, abs_inv, abs_of_nonneg (raw_l2norm_nonneg x),
    inv_mul_cancel₀ (raw_l2norm_ne_zero hx)]

lemma raw_normalized_trilinear {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) :
    trilinear A ((l2norm x)⁻¹ • x) ((l2norm y)⁻¹ • y) ((l2norm z)⁻¹ • z) =
      trilinear A x y z / (l2norm x * l2norm y * l2norm z) := by
  simp only [raw_trilinear_smul1, raw_trilinear_smul2, raw_trilinear_smul3,
    div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

lemma unit_abs_le {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) {M : ℝ}
    (hM : IsGreatest {t : ℝ | ∃ (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ),
      l2norm x = 1 ∧ l2norm y = 1 ∧ l2norm z = 1 ∧ t = trilinear A x y z} M)
    (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ)
    (hx : l2norm x = 1) (hy : l2norm y = 1) (hz : l2norm z = 1) :
    |trilinear A x y z| ≤ M := by
  have hp : trilinear A x y z ≤ M := hM.2 ⟨x, y, z, hx, hy, hz, rfl⟩
  have hn : -trilinear A x y z ≤ M := hM.2
    ⟨(-1 : ℝ) • x, y, z,
      by simpa only [raw_l2norm_smul, abs_neg, abs_one, one_mul] using hx,
      hy, hz, by simp only [raw_trilinear_smul1, neg_one_mul]⟩
  exact abs_le.mpr ⟨by linarith, hp⟩

lemma unit_greatest_specNorm {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) {M : ℝ}
    (hM : IsGreatest {t : ℝ | ∃ (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ),
      l2norm x = 1 ∧ l2norm y = 1 ∧ l2norm z = 1 ∧ t = trilinear A x y z} M) :
    specNorm A = M := by
  apply IsGreatest.csSup_eq
  refine ⟨?_, ?_⟩
  · obtain ⟨x, y, z, hx, hy, hz, he⟩ := hM.1
    have hnonneg : 0 ≤ M := (abs_nonneg _).trans (unit_abs_le A hM x y z hx hy hz)
    refine ⟨x, y, z, raw_ne_zero_of_unit x hx, raw_ne_zero_of_unit y hy, raw_ne_zero_of_unit z hz, ?_⟩
    simp [hx, hy, hz, ← he, abs_of_nonneg hnonneg]
  · rintro t ⟨x, y, z, hx, hy, hz, rfl⟩
    have h := unit_abs_le A hM ((l2norm x)⁻¹ • x) ((l2norm y)⁻¹ • y) ((l2norm z)⁻¹ • z)
      (raw_normalized_unit hx) (raw_normalized_unit hy) (raw_normalized_unit hz)
    simpa only [raw_normalized_trilinear, abs_div,
      abs_of_nonneg (mul_nonneg (mul_nonneg (raw_l2norm_nonneg x) (raw_l2norm_nonneg y))
        (raw_l2norm_nonneg z))] using h
end TensorSpectralCommon



open scoped BigOperators
open TensorNP.SpectralNorm Matrix Finset

lemma sum_blocks (l e : ℕ) (f : Fin (l + 2 * e) → ℝ) :
    ∑ k, f k =
      (∑ i : Fin l, f ⟨i.val, by omega⟩) +
      (∑ i : Fin e, f ⟨l + i.val, by omega⟩) +
      (∑ i : Fin e, f ⟨e + l + i.val, by omega⟩) := by
  have h : (∑ k : Fin ((l + e) + e), f ⟨k.val, by omega⟩) =
      (∑ i : Fin l, f ⟨i.val, by omega⟩) +
      (∑ i : Fin e, f ⟨l + i.val, by omega⟩) +
      (∑ i : Fin e, f ⟨e + l + i.val, by omega⟩) := by
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.val_castAdd, Fin.val_natAdd, Nat.add_comm e l]
  have heq : l + 2 * e = (l + e) + e := by omega
  exact (Fintype.sum_equiv (finCongr heq) f (fun k => f ⟨k.val, by omega⟩) (fun _ => rfl)).trans h

lemma edgeMatrix_cast {v : ℕ} (s : Sym2 (Fin v)) (i j : Fin v) :
    (edgeMatrix ℚ s i j : ℝ) = edgeMatrix ℝ s i j := by
  simp [edgeMatrix, Matrix.of_apply, apply_ite]

lemma clique_slice_first {v e : ℕ} (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (r : Fin l) :
    (fun i j => (cliqueTensor G ε l i j ⟨r.val, by omega⟩ : ℝ)) =
      (1 / (l : ℝ)) • (1 : Matrix (Fin v) (Fin v) ℝ) := by
  exact Matrix.ext (fun i j => by simp +contextual [cliqueTensor, r.isLt, Matrix.smul_apply, Matrix.one_apply, apply_ite])

lemma clique_slice_second {v e : ℕ} (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (r : Fin e) :
    (fun i j => (cliqueTensor G ε l i j ⟨l + r.val, by omega⟩ : ℝ)) =
      edgeMatrix ℝ (ε r : Sym2 (Fin v)) := by
  exact Matrix.ext (fun i j => by
    simp [cliqueTensor, show ¬ l + r.val < l by omega,
      show l + r.val < l + e by omega, edgeMatrix_cast])

lemma clique_slice_third {v e : ℕ} (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (r : Fin e) :
    (fun i j => (cliqueTensor G ε l i j ⟨e + l + r.val, by omega⟩ : ℝ)) =
      edgeMatrix ℝ (ε r : Sym2 (Fin v)) := by
  exact Matrix.ext (fun i j => by
    simp [cliqueTensor, show ¬ e + l + r.val < l by omega,
      show ¬ e + l + r.val < l + e by omega,
      show e + l + r.val - l - e = r.val by omega, edgeMatrix_cast])

lemma trilinear_slices {a b c : ℕ} (A : Fin a → Fin b → Fin c → ℝ)
    (x : Fin a → ℝ) (y : Fin b → ℝ) (z : Fin c → ℝ) :
    trilinear A x y z = ∑ k, (x ⬝ᵥ ((fun i j => A i j k) *ᵥ y)) * z k := by
  simp only [trilinear, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]


theorem cliqueTensor_trilinear {v e : ℕ} (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (x y : Fin v → ℝ) (w : Fin (l + 2*e) → ℝ) :
    trilinear (fun i j k => (cliqueTensor G ε l i j k : ℝ)) x y w = form26 G ε l x y w := by
  rw [trilinear_slices, sum_blocks]
  simp only [clique_slice_first, clique_slice_second, clique_slice_third, form26]


open scoped BigOperators
open TensorNP.SpectralNorm Set Metric

namespace TensorSpectralCommon

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma norm_eq_l2 {n : ℕ} (u : E n) : ‖u‖ = l2norm u := by
  simpa [l2norm] using EuclideanSpace.norm_eq u

lemma linear_max_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a x : H) (M : ℝ) (hx : ‖x‖ = 1) (hax : inner ℝ a x = M)
    (hmax : ∀ u : H, ‖u‖ = 1 → inner ℝ a u ≤ M) : a = M • x := by
  have hnorm : ‖a‖ ≤ M := by
    by_cases ha : a = 0
    · simpa [ha] using hax.le
    · have hu : ‖(‖a‖⁻¹ : ℝ) • a‖ = 1 := by simp [norm_smul, norm_ne_zero_iff.mpr ha]
      simpa [inner_smul_right, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc, norm_ne_zero_iff.mpr ha] using hmax ((‖a‖⁻¹ : ℝ) • a) hu
  have hlow : M ≤ ‖a‖ := by simpa only [hax, hx, mul_one] using real_inner_le_norm a x
  have hn : ‖a‖ = M := le_antisymm hnorm hlow
  simpa only [hx, one_smul, hn] using
    (inner_eq_norm_mul_iff_real (x := a) (y := x)).mp (by simpa only [hn, hx, mul_one] using hax)

noncomputable def contract1 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (y : E m) (z : E n) : E l := WithLp.toLp 2 fun i => ∑ j, ∑ k, A i j k*y j*z k

noncomputable def contract2 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (x : E l) (z : E n) : E m := WithLp.toLp 2 fun j => ∑ i, ∑ k, A i j k*x i*z k

noncomputable def contract3 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (x : E l) (y : E m) : E n := WithLp.toLp 2 fun k => ∑ i, ∑ j, A i j k*x i*y j

lemma inner_contract1 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (x : E l) (y : E m) (z : E n) :
    inner ℝ (contract1 A y z) x = trilinear A x y z := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, contract1, trilinear, dotProduct, Finset.mul_sum, mul_left_comm, mul_assoc]

lemma inner_contract2 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (x : E l) (y : E m) (z : E n) :
    inner ℝ (contract2 A x z) y = trilinear A x y z := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, contract2, trilinear, dotProduct, star_trivial, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_left_comm, mul_assoc]

lemma inner_contract3 {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (x : E l) (y : E m) (z : E n) :
    inner ℝ (contract3 A x y) z = trilinear A x y z := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, contract3, trilinear, dotProduct, star_trivial, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  simp [mul_comm, mul_assoc]

lemma continuous_trilinear {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ) :
    Continuous (fun p : E l × E m × E n => trilinear A p.1 p.2.1 p.2.2) := by
  unfold trilinear
  fun_prop

lemma exists_unit_greatest {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    (hl : 0 < l) (hm : 0 < m) (hn : 0 < n) :
    ∃ M : ℝ, IsGreatest {t : ℝ | ∃ (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ),
      l2norm x = 1 ∧ l2norm y = 1 ∧ l2norm z = 1 ∧ t = trilinear A x y z} M := by
  have : NeZero l := ⟨ne_of_gt hl⟩
  have : NeZero m := ⟨ne_of_gt hm⟩
  have : NeZero n := ⟨ne_of_gt hn⟩
  have hc := (isCompact_sphere (0 : E l) 1).prod
    ((isCompact_sphere (0 : E m) 1).prod (isCompact_sphere (0 : E n) 1))
  have hne : (sphere (0 : E l) 1 ×ˢ sphere (0 : E m) 1 ×ˢ sphere (0 : E n) 1).Nonempty :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).prod
      ((NormedSpace.sphere_nonempty.mpr zero_le_one).prod (NormedSpace.sphere_nonempty.mpr zero_le_one))
  obtain ⟨p, hp, hmax⟩ := hc.exists_isMaxOn hne (continuous_trilinear A).continuousOn
  refine ⟨trilinear A p.1 p.2.1 p.2.2,
    ⟨p.1, p.2.1, p.2.2,
      (norm_eq_l2 p.1).symm.trans (mem_sphere_zero_iff_norm.mp hp.1),
      (norm_eq_l2 p.2.1).symm.trans (mem_sphere_zero_iff_norm.mp hp.2.1),
      (norm_eq_l2 p.2.2).symm.trans (mem_sphere_zero_iff_norm.mp hp.2.2), rfl⟩, ?_⟩
  rintro t ⟨u, v, w, hu, hv, hw, rfl⟩
  exact hmax (a := (WithLp.toLp 2 u, WithLp.toLp 2 v, WithLp.toLp 2 w))
    ⟨mem_sphere_zero_iff_norm.mpr ((norm_eq_l2 _).trans hu),
      mem_sphere_zero_iff_norm.mpr ((norm_eq_l2 _).trans hv),
      mem_sphere_zero_iff_norm.mpr ((norm_eq_l2 _).trans hw)⟩

lemma unit_greatest_is_singular {l m n : ℕ} (A : Fin l → Fin m → Fin n → ℝ)
    {M : ℝ} (hM : IsGreatest {t : ℝ | ∃ (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ),
      l2norm x = 1 ∧ l2norm y = 1 ∧ l2norm z = 1 ∧ t = trilinear A x y z} M) :
    IsUnitSingularValue A M := by
  obtain ⟨x, y, z, hx, hy, hz, hval⟩ := hM.1
  have h1 : contract1 A (WithLp.toLp 2 y) (WithLp.toLp 2 z) = M • WithLp.toLp 2 x :=
    linear_max_eq _ _ M (by simpa only [norm_eq_l2] using hx)
      (by simpa only [inner_contract1] using hval.symm)
      (fun u hu => by simpa only [inner_contract1] using
        (hM.2 ⟨u, y, z, (norm_eq_l2 u).symm.trans hu, hy, hz, rfl⟩))
  have h2 : contract2 A (WithLp.toLp 2 x) (WithLp.toLp 2 z) = M • WithLp.toLp 2 y :=
    linear_max_eq _ _ M (by simpa only [norm_eq_l2] using hy)
      (by simpa only [inner_contract2] using hval.symm)
      (fun u hu => by simpa only [inner_contract2] using
        (hM.2 ⟨x, u, z, hx, (norm_eq_l2 u).symm.trans hu, hz, rfl⟩))
  have h3 : contract3 A (WithLp.toLp 2 x) (WithLp.toLp 2 y) = M • WithLp.toLp 2 z :=
    linear_max_eq _ _ M (by simpa only [norm_eq_l2] using hz)
      (by simpa only [inner_contract3] using hval.symm)
      (fun u hu => by simpa only [inner_contract3] using
        (hM.2 ⟨x, y, u, hx, hy, (norm_eq_l2 u).symm.trans hu, rfl⟩))
  exact ⟨x, y, z, hx, hy, hz,
    fun i => congrArg (fun u : E l => u i) h1,
    fun j => congrArg (fun u : E m => u j) h2,
    fun k => congrArg (fun u : E n => u k) h3⟩

end TensorSpectralCommon



open scoped BigOperators
open TensorNP.SpectralNorm

namespace SpectralSingular

theorem singular_trilinear_value {a b c : ℕ} (A : Fin a → Fin b → Fin c → ℝ)
    (x : Fin a → ℝ) (y : Fin b → ℝ) (z : Fin c → ℝ) (σ : ℝ)
    (hx : l2norm x = 1)
    (hcon : ∀ i, ∑ j, ∑ k, A i j k * y j * z k = σ * x i) :
    trilinear A x y z = σ := by
  have hs : (∑ i, x i ^ 2) = 1 := Real.sqrt_eq_one.mp hx
  have hf (i : Fin a) (j : Fin b) (k : Fin c) :
      A i j k * x i * y j * z k = x i * (A i j k * y j * z k) := by ring
  unfold trilinear
  simp_rw [hf, ← Finset.mul_sum, hcon]
  have hg (i : Fin a) : x i * (σ * x i) = σ * x i ^ 2 := by ring
  simp_rw [hg, ← Finset.mul_sum, hs, mul_one]

end SpectralSingular


open TensorNP.SpectralNorm

namespace SpectralSingular

theorem unit_greatest_singular_bound {l m n : ℕ}
    (A : Fin l → Fin m → Fin n → ℝ) {M σ : ℝ}
    (hM : IsGreatest {t : ℝ | ∃ (x : Fin l → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ),
      l2norm x = 1 ∧ l2norm y = 1 ∧ l2norm z = 1 ∧ t = trilinear A x y z} M)
    (hs : IsUnitSingularValue A σ) : |σ| ≤ M := by
  exact match hs with
  | ⟨x, y, z, hx, hy, hz, hcon, _, _⟩ =>
      (congrArg abs (singular_trilinear_value A x y z σ hx hcon)).symm.le.trans
        (TensorSpectralCommon.unit_abs_le A hM x y z hx hy hz)

end SpectralSingular

open TensorNP.SpectralNorm

theorem solution {v e : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    (ε : Fin e ≃ G.edgeSet) (l : ℕ) (hl : 1 ≤ l) :
    specNorm (fun i j k => (cliqueTensor G ε l i j k : ℝ)) = Tval G ε l ∧
      IsUnitSingularValue (fun i j k => (cliqueTensor G ε l i j k : ℝ)) (Tval G ε l) ∧
      ∀ σ : ℝ, IsUnitSingularValue (fun i j k => (cliqueTensor G ε l i j k : ℝ)) σ →
        |σ| ≤ Tval G ε l  := by
  classical
  let A : Fin v → Fin v → Fin (l + 2 * e) → ℝ := fun i j k => (cliqueTensor G ε l i j k : ℝ)
  obtain ⟨M, hM⟩ := TensorSpectralCommon.exists_unit_greatest A hv hv (by omega)
  have hMform : IsGreatest {t : ℝ | ∃ (x y : Fin v → ℝ) (w : Fin (l + 2 * e) → ℝ),
      l2norm x = 1 ∧ l2norm y = 1 ∧ l2norm w = 1 ∧ t = form26 G ε l x y w} M := by
    simpa only [A, cliqueTensor_trilinear] using hM
  have hT : M = Tval G ε l := hMform.csSup_eq.symm
  refine ⟨(TensorSpectralCommon.unit_greatest_specNorm A hM).trans hT, ?_, ?_⟩
  · simpa only [hT] using TensorSpectralCommon.unit_greatest_is_singular A hM
  · intro σ hs
    simpa only [hT] using SpectralSingular.unit_greatest_singular_bound A hM hs
