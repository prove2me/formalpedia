-- Prove2me | solution 1 for StrongConv.prob_norm_adjPerp_le_highDegree_ge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T00:46:25.97163+00:00
-- url     : https://prove2.me/submissions/de3ca717-6c57-4d30-b62b-03401f840b44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_BrailovskayaVanHandel_prob_norm_sum_gt_le

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
/-!
# Blueprint: Brailovskaya–van Handel Theorem 3.8 from their Corollary 2.17

`bvh_cor217` is the standalone statement `BrailovskayaVanHandel.prob_norm_sum_gt_le` (copied here
as an assumed stub until it is published). Apply it to `D = N`, `n = d`, `Ω = S_N` and
`Zᵢ(τ) = Π_τ + Π_τᵀ − (2/N)J`, whose sum has the norm of `Aᴺ`; the parameters are
`σ² = 2dN/(N − 1)`, `σ_*², v² ≤ 4d/(N − 1)`, `R ≤ 4`; take `t = (a + 1) log N + log 4`.
-/
/-- The permutation matrix of `τ`: column `b` is `e_{τ b}` (as `permOp`). -/
def permMat {N : ℕ} (τ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => if τ b = a then 1 else 0

/-- The centred summand `Π_τ + Π_τᵀ − (2/N)J`. -/
def zMat {N : ℕ} (τ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  permMat τ + (permMat τ)ᴴ - ((2 : ℂ) / N) • Matrix.of (fun _ _ => (1 : ℂ))

/-- The random matrix `Y(σ) = ∑ᵢ zMat (σ i)`. -/
def yMat {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ i, zMat (σ i)

end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
namespace PartQM
/-! ### Counting over permutations -/
lemma sum_perm_apply_indep {N : ℕ} {M : Type*} [AddCommMonoid M] (g : Fin N → M) (b b' : Fin N) :
    ∑ τ : Equiv.Perm (Fin N), g (τ b) = ∑ τ : Equiv.Perm (Fin N), g (τ b') := by
  refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap b b')) _ _ fun τ => ?_
  simp [Equiv.Perm.mul_apply]

lemma card_perm_C (N : ℕ) : ((Fintype.card (Equiv.Perm (Fin N)) : ℕ) : ℂ) = (N.factorial : ℂ) := by
  rw [Fintype.card_perm, Fintype.card_fin]

/-- One-point sums. -/
lemma sum_perm_one {N : ℕ} (g : Fin N → ℂ) (b : Fin N) :
    (N : ℂ) * ∑ τ : Equiv.Perm (Fin N), g (τ b) = N.factorial * ∑ a, g a := by
  have h1 : (N : ℂ) * ∑ τ : Equiv.Perm (Fin N), g (τ b) =
      ∑ b' : Fin N, ∑ τ : Equiv.Perm (Fin N), g (τ b') := by
    rw [Finset.sum_congr rfl fun b' _ => (sum_perm_apply_indep g b b').symm]
    simp
  rw [h1, Finset.sum_comm]
  have : ∀ τ : Equiv.Perm (Fin N), ∑ b', g (τ b') = ∑ a, g a := fun τ =>
    Equiv.sum_comp τ g
  rw [Finset.sum_congr rfl fun τ _ => this τ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_perm_C]

lemma sum_perm_two_indep {N : ℕ} (g : Fin N → Fin N → ℂ) (b b' b'' : Fin N) (h' : b' ≠ b)
    (h'' : b'' ≠ b) :
    ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b') = ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b'') := by
  refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap b' b'')) _ _ fun τ => ?_
  simp only [Equiv.coe_mulRight, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h'.symm h''.symm]

/-- Two-point sums. -/
lemma sum_perm_two {N : ℕ} (g : Fin N → Fin N → ℂ) (b b' : Fin N) (hb : b' ≠ b) :
    ((N : ℂ) * (N - 1)) * ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b') =
      N.factorial * ∑ a, ∑ a' ∈ Finset.univ.erase a, g a a' := by
  have hcard : ((Finset.univ.erase b).card : ℂ) = (N : ℂ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ N := by have := b.isLt; omega
    push_cast [Nat.cast_sub this]; ring
  have h1 : ((N : ℂ) - 1) * ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b') =
      ∑ b'' ∈ Finset.univ.erase b, ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b'') := by
    rw [Finset.sum_congr rfl fun b'' hb'' =>
      (sum_perm_two_indep g b b' b'' hb (Finset.ne_of_mem_erase hb'')).symm]
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have h2 : ∀ τ : Equiv.Perm (Fin N), ∑ b'' ∈ Finset.univ.erase b, g (τ b) (τ b'') =
      ∑ a' ∈ Finset.univ.erase (τ b), g (τ b) a' := by
    intro τ
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_erase_eq_sub (Finset.mem_univ _),
      Equiv.sum_comp τ (g (τ b))]
  calc ((N : ℂ) * (N - 1)) * ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b')
      = (N : ℂ) * (((N : ℂ) - 1) * ∑ τ : Equiv.Perm (Fin N), g (τ b) (τ b')) := by ring
    _ = (N : ℂ) * ∑ τ : Equiv.Perm (Fin N), ∑ a' ∈ Finset.univ.erase (τ b), g (τ b) a' := by
        rw [h1, Finset.sum_comm, Finset.sum_congr rfl fun τ _ => h2 τ]
    _ = N.factorial * ∑ a, ∑ a' ∈ Finset.univ.erase a, g a a' :=
        sum_perm_one (fun a => ∑ a' ∈ Finset.univ.erase a, g a a') b

/-- `∑_τ f(τ(τ b)) = N (N-2)! f(b)` for `f` of sum zero. -/
lemma sum_perm_sq_apply {N : ℕ} (f : Fin N → ℂ) (hf : ∑ a, f a = 0) (b : Fin N) :
    ((N : ℂ) - 1) * ∑ τ : Equiv.Perm (Fin N), f (τ (τ b)) = N.factorial * f b := by
  have hN : (N : ℂ) ≠ 0 := by
    have := b.isLt; exact_mod_cast (show N ≠ 0 by omega)
  have hsplit : ∀ τ : Equiv.Perm (Fin N), f (τ (τ b)) =
      ∑ c, (if τ b = c then f (τ c) else 0) := by
    intro τ; rw [Finset.sum_ite_eq]; simp
  have hc : ∀ c ∈ Finset.univ.erase b, ((N : ℂ) * (N - 1)) *
      ∑ τ : Equiv.Perm (Fin N), (if τ b = c then f (τ c) else 0) = - (N.factorial * f c) := by
    intro c hc
    have := sum_perm_two (fun u v => if u = c then f v else 0) b c (Finset.ne_of_mem_erase hc)
    rw [this]
    have h3 : ∀ a, ∑ a' ∈ Finset.univ.erase a, (if a = c then f a' else 0) =
        if a = c then ∑ a' ∈ Finset.univ.erase a, f a' else 0 := by
      intro a; split_ifs <;> simp
    rw [Finset.sum_congr rfl fun a _ => h3 a, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), hf]
    ring
  have hb : (N : ℂ) * ∑ τ : Equiv.Perm (Fin N), (if τ b = b then f (τ b) else 0) =
      N.factorial * f b := by
    rw [sum_perm_one (fun a => if a = b then f a else 0) b]
    simp
  apply mul_left_cancel₀ hN
  rw [Finset.sum_congr rfl fun τ _ => hsplit τ, Finset.sum_comm,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  have hrest : (N : ℂ) * (((N : ℂ) - 1) * ∑ c ∈ Finset.univ.erase b,
      ∑ τ : Equiv.Perm (Fin N), (if τ b = c then f (τ c) else 0)) = N.factorial * f b := by
    rw [← mul_assoc, Finset.mul_sum, Finset.sum_congr rfl hc, Finset.sum_neg_distrib,
      ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ _), hf]
    ring
  have hb' : ∑ τ : Equiv.Perm (Fin N), (if τ b = b then f (τ b) else 0) =
      ∑ τ : Equiv.Perm (Fin N), (if τ b = b then f (τ b) else 0) := rfl
  calc (N : ℂ) * (((N : ℂ) - 1) * (∑ τ : Equiv.Perm (Fin N), (if τ b = b then f (τ b) else 0) +
        ∑ c ∈ Finset.univ.erase b, ∑ τ : Equiv.Perm (Fin N), (if τ b = c then f (τ c) else 0)))
      = ((N : ℂ) - 1) * ((N : ℂ) * ∑ τ : Equiv.Perm (Fin N), (if τ b = b then f (τ b) else 0)) +
        (N : ℂ) * (((N : ℂ) - 1) * ∑ c ∈ Finset.univ.erase b,
          ∑ τ : Equiv.Perm (Fin N), (if τ b = c then f (τ c) else 0)) := by ring
    _ = (N : ℂ) * (N.factorial * f b) := by rw [hb, hrest]; ring

/-! ### Coordinates -/
lemma permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply, mul_apply_eq_comp]
  rfl

lemma permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

lemma permOpPerp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : OnesPerp N) :
    (permOpPerp π x : EuclideanSpace ℂ (Fin N)) = permOp π x := rfl

lemma inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪permOp π x, y⟫_ℂ = ⟪x, permOp π⁻¹ y⟫_ℂ := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

lemma star_permOpPerp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    star (permOpPerp π) = permOpPerp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, permOpPerp_apply]
  rw [inner_permOp, inv_inv]

lemma zMat_entry {N : ℕ} (τ : Equiv.Perm (Fin N)) (a b : Fin N) :
    zMat τ a b = (if τ b = a then 1 else 0) + (if τ a = b then 1 else 0) - 2 / N := by
  simp only [zMat, permMat, Matrix.sub_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one]
  congr 2
  split_ifs <;> simp

lemma zMat_mulVec {N : ℕ} (τ : Equiv.Perm (Fin N)) (x : Fin N → ℂ) (a : Fin N) :
    (zMat τ *ᵥ x) a = x (τ.symm a) + x (τ a) - (2 / N) * ∑ b, x b := by
  simp only [Matrix.mulVec, dotProduct, zMat_entry, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.mul_sum]
  congr 2
  · rw [Finset.sum_eq_single (τ.symm a)]
    · simp
    · intro b _ hb; rw [if_neg]
      intro h; exact hb (by rw [← h]; simp)
    · simp
  · rw [Finset.sum_ite_eq]; simp

lemma toE_zMat_apply {N : ℕ} (τ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (a : Fin N) :
    toEuclideanCLM (𝕜 := ℂ) (zMat τ) x a = x (τ.symm a) + x (τ a) - (2 / N) * ∑ b, x b := by
  have := zMat_mulVec τ (WithLp.ofLp x) a
  simpa using this

lemma toE_yMat_apply {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N))
    (a : Fin N) :
    toEuclideanCLM (𝕜 := ℂ) (yMat σ) x a =
      ∑ i, (x ((σ i).symm a) + x (σ i a) - (2 / N) * ∑ b, x b) := by
  simp only [yMat, map_sum, _root_.sum_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [toE_zMat_apply]

lemma mem_onesPerp_iff {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) :
    x ∈ OnesPerp N ↔ ∑ b, x b = 0 := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [onesVec, PiLp.inner_apply]

lemma adjPerp_coe_apply {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : OnesPerp N) (a : Fin N) :
    (adjPerp σ x : EuclideanSpace ℂ (Fin N)) a = ∑ i, ((x : EuclideanSpace ℂ (Fin N)) ((σ i).symm a) +
      (x : EuclideanSpace ℂ (Fin N)) (σ i a)) := by
  simp only [adjPerp, sModel, star_permOpPerp, _root_.sum_apply,
    _root_.add_apply, Submodule.coe_sum, Submodule.coe_add, permOpPerp_apply]
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [permOp_apply, Equiv.Perm.inv_def]

/-! ### Part Q -/
lemma toE_yMat_onesVec {d N : ℕ} (hN : 1 ≤ N) (σ : Fin d → Equiv.Perm (Fin N)) :
    toEuclideanCLM (𝕜 := ℂ) (yMat σ) (onesVec N) = 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  ext a
  rw [toE_yMat_apply]
  simp only [onesVec, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [div_mul_cancel₀ _ hN']
  simp only [WithLp.ofLp_zero, Pi.zero_apply]
  ring

theorem norm_yMat_eq {d N : ℕ} (hN : 1 ≤ N) (σ : Fin d → Equiv.Perm (Fin N)) :
    ‖toEuclideanCLM (𝕜 := ℂ) (yMat σ)‖ = ‖adjPerp σ‖ := by
  set Y := toEuclideanCLM (𝕜 := ℂ) (yMat σ) with hY
  have hagree : ∀ x : OnesPerp N, Y x = (adjPerp σ x : EuclideanSpace ℂ (Fin N)) := by
    intro x; ext a
    rw [hY, toE_yMat_apply, adjPerp_coe_apply, (mem_onesPerp_iff _).1 x.2]
    simp
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    set K := OnesPerp N
    have hx : Y x = Y (K.orthogonalProjectionOnto x : EuclideanSpace ℂ (Fin N)) := by
      have hmem : x - K.starProjection x ∈ (ℂ ∙ onesVec N) := by
        have := K.sub_starProjection_mem_orthogonal x
        rwa [Submodule.orthogonal_orthogonal] at this
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have h0 : Y (x - K.starProjection x) = 0 := by
        rw [← hc, map_smul, hY, toE_yMat_onesVec hN, smul_zero]
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    rw [hx, hagree]
    calc ‖(adjPerp σ (K.orthogonalProjectionOnto x) : EuclideanSpace ℂ (Fin N))‖
        = ‖adjPerp σ (K.orthogonalProjectionOnto x)‖ := rfl
      _ ≤ ‖adjPerp σ‖ * ‖K.orthogonalProjectionOnto x‖ := (adjPerp σ).le_opNorm _
      _ ≤ ‖adjPerp σ‖ * ‖x‖ := mul_le_mul_of_nonneg_left
          (K.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _)
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖adjPerp σ x‖ = ‖Y x‖ := by rw [hagree]; rfl
      _ ≤ ‖Y‖ * ‖(x : EuclideanSpace ℂ (Fin N))‖ := Y.le_opNorm _
      _ = ‖Y‖ * ‖x‖ := rfl

end PartQM
end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
/-! ## Part Q: `‖Y(σ)‖ = ‖Aᴺ‖` -/
alias norm_yMat_eq := StrongConv.HighDegUp.PartQM.norm_yMat_eq

end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
namespace PartQM
/-! ### Part M: easy facts -/
theorem zMat_isHermitian {N : ℕ} (τ : Equiv.Perm (Fin N)) : (zMat τ).IsHermitian := by
  ext a b
  rw [Matrix.conjTranspose_apply, zMat_entry, zMat_entry]
  simp only [star_sub, star_add, apply_ite star, star_one, star_zero, star_div₀, star_ofNat,
    star_natCast]
  ring

end PartQM
end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
/-! ## Part M: the parameters of the model -/
alias zMat_isHermitian := StrongConv.HighDegUp.PartQM.zMat_isHermitian

end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
namespace PartQM
theorem sum_zMat {N : ℕ} (hN : 1 ≤ N) : ∑ τ : Equiv.Perm (Fin N), zMat τ = 0 := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  ext a b
  rw [Matrix.sum_apply, Matrix.zero_apply]
  simp only [zMat_entry]
  apply mul_left_cancel₀ hN'
  rw [mul_zero, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub, mul_add,
    sum_perm_one (fun c => if c = a then (1 : ℂ) else 0) b]
  have h2 : ∑ τ : Equiv.Perm (Fin N), (if τ a = b then (1 : ℂ) else 0) =
      ∑ τ : Equiv.Perm (Fin N), (fun c => if c = b then (1 : ℂ) else 0) (τ a) := rfl
  rw [h2, sum_perm_one (fun c => if c = b then (1 : ℂ) else 0) a]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, card_perm_C]
  field_simp
  ring

end PartQM
end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
alias sum_zMat := StrongConv.HighDegUp.PartQM.sum_zMat

end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
namespace PartQM
lemma toE_zMat_eq {N : ℕ} (τ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) :
    toEuclideanCLM (𝕜 := ℂ) (zMat τ) x =
      permOp τ x + permOp τ⁻¹ x - ((2 / N : ℂ) * ⟪onesVec N, x⟫_ℂ) • onesVec N := by
  ext a
  rw [toE_zMat_apply]
  simp [permOp_apply, onesVec, PiLp.inner_apply, Equiv.Perm.inv_def]

lemma norm_onesVec_sq (N : ℕ) : ‖onesVec N‖ ^ 2 = N := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [onesVec]

lemma norm_permOp_apply {N : ℕ} (τ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) :
    ‖permOp τ x‖ = ‖x‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ τ).norm_map x

theorem norm_zMat_le {N : ℕ} (τ : Equiv.Perm (Fin N)) : ‖toEuclideanCLM (𝕜 := ℂ) (zMat τ)‖ ≤ 4 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
  rw [toE_zMat_eq]
  have hJ : ‖((2 / N : ℂ) * ⟪onesVec N, x⟫_ℂ) • onesVec N‖ ≤ 2 * ‖x‖ := by
    rw [norm_smul, norm_mul]
    have h1 := norm_inner_le_norm (𝕜 := ℂ) (onesVec N) x
    have h2 : ‖(2 / N : ℂ)‖ * ‖onesVec N‖ ^ 2 ≤ 2 := by
      rw [norm_onesVec_sq]
      rcases Nat.eq_zero_or_pos N with h | h
      · subst h; simp
      · rw [norm_div]; simp only [Complex.norm_ofNat, Complex.norm_natCast]
        rw [div_mul_cancel₀]; exact_mod_cast h.ne'
    calc ‖(2 / N : ℂ)‖ * ‖⟪onesVec N, x⟫_ℂ‖ * ‖onesVec N‖
        ≤ ‖(2 / N : ℂ)‖ * (‖onesVec N‖ * ‖x‖) * ‖onesVec N‖ := by gcongr
      _ = (‖(2 / N : ℂ)‖ * ‖onesVec N‖ ^ 2) * ‖x‖ := by ring
      _ ≤ 2 * ‖x‖ := by gcongr
  calc ‖permOp τ x + permOp τ⁻¹ x - ((2 / N : ℂ) * ⟪onesVec N, x⟫_ℂ) • onesVec N‖
      ≤ ‖permOp τ x‖ + ‖permOp τ⁻¹ x‖ + ‖((2 / N : ℂ) * ⟪onesVec N, x⟫_ℂ) • onesVec N‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ‖x‖ + ‖x‖ + 2 * ‖x‖ := by rw [norm_permOp_apply, norm_permOp_apply]; gcongr
    _ = 4 * ‖x‖ := by ring

end PartQM
end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
alias norm_zMat_le := StrongConv.HighDegUp.PartQM.norm_zMat_le

end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
namespace PartQM
/-! ### Operator norms from Gram-type bounds -/
lemma opNorm_le_of_gram {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]
    (A : E →L[ℂ] E) (f : ι → E → F) (K c : ℝ) (hK : 0 < K) (hc : 0 ≤ c)
    (hA : ∀ x, ‖A x‖ ^ 2 ≤ K⁻¹ * ∑ ω, ‖f ω (A x)‖ * ‖f ω x‖)
    (hf : ∀ x, K⁻¹ * ∑ ω, ‖f ω x‖ ^ 2 ≤ c * ‖x‖ ^ 2) : ‖A‖ ≤ c := by
  refine A.opNorm_le_bound hc fun x => ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun ω => ‖f ω (A x)‖)
    (fun ω => ‖f ω x‖)
  have h0 : 0 ≤ ‖A x‖ ^ 2 := by positivity
  have hK' : 0 ≤ K⁻¹ := inv_nonneg.2 hK.le
  have h1 : (‖A x‖ ^ 2) ^ 2 ≤ (c * ‖A x‖ ^ 2) * (c * ‖x‖ ^ 2) := by
    calc (‖A x‖ ^ 2) ^ 2 ≤ (K⁻¹ * ∑ ω, ‖f ω (A x)‖ * ‖f ω x‖) ^ 2 :=
          pow_le_pow_left₀ h0 (hA x) 2
      _ = K⁻¹ ^ 2 * (∑ ω, ‖f ω (A x)‖ * ‖f ω x‖) ^ 2 := by ring
      _ ≤ K⁻¹ ^ 2 * ((∑ ω, ‖f ω (A x)‖ ^ 2) * (∑ ω, ‖f ω x‖ ^ 2)) := by gcongr
      _ = (K⁻¹ * ∑ ω, ‖f ω (A x)‖ ^ 2) * (K⁻¹ * ∑ ω, ‖f ω x‖ ^ 2) := by ring
      _ ≤ (c * ‖A x‖ ^ 2) * (c * ‖x‖ ^ 2) :=
          mul_le_mul (hf _) (hf _) (by positivity) (by positivity)
  rcases eq_or_lt_of_le (norm_nonneg (A x)) with h | h
  · rw [← h]; positivity
  have h2 : ‖A x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    have hpos : 0 < ‖A x‖ ^ 2 := by positivity
    have : ‖A x‖ ^ 2 * ‖A x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 * ‖A x‖ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

/-! ### Independence -/
lemma sum_inner_off {X F : Type*} [Fintype X] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {d : ℕ} (u : X → F) (hu : ∑ x, u x = 0) (i j : Fin d) (hij : j ≠ i) :
    ∑ σ : Fin d → X, ⟪u (σ i), u (σ j)⟫_ℂ = 0 := by
  rw [← (Equiv.funSplitAt i X).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  simp only [Equiv.funSplitAt_symm_apply, dif_neg hij, dite_true]
  rw [← sum_inner, hu, inner_zero_left]

lemma sum_diag {X : Type*} [Fintype X] {d : ℕ} (g : X → ℝ) (i : Fin d) :
    (Fintype.card X : ℝ) * ∑ σ : Fin d → X, g (σ i) =
      Fintype.card (Fin d → X) * ∑ x, g x := by
  rw [← (Equiv.funSplitAt i X).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.funSplitAt_symm_apply, dite_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [Fintype.card_congr (Equiv.funSplitAt i X), Fintype.card_prod, ← Finset.mul_sum]
  push_cast; ring

lemma sum_norm_sum_sq {X F : Type*} [Fintype X] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {d : ℕ} (u : X → F) (hu : ∑ x, u x = 0) :
    (Fintype.card X : ℝ) * ∑ σ : Fin d → X, ‖∑ i, u (σ i)‖ ^ 2 =
      d * Fintype.card (Fin d → X) * ∑ x, ‖u x‖ ^ 2 := by
  have hexp : ∀ σ : Fin d → X, ‖∑ i, u (σ i)‖ ^ 2 =
      ∑ i, ∑ j, RCLike.re ⟪u (σ i), u (σ j)⟫_ℂ := by
    intro σ
    rw [@norm_sq_eq_re_inner ℂ, sum_inner]
    simp only [inner_sum, map_sum]
  simp only [hexp]
  rw [Finset.sum_comm, Finset.mul_sum]
  have : ∀ i : Fin d, (Fintype.card X : ℝ) * ∑ σ : Fin d → X, ∑ j, RCLike.re ⟪u (σ i), u (σ j)⟫_ℂ
      = Fintype.card (Fin d → X) * ∑ x, ‖u x‖ ^ 2 := by
    intro i
    rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [Finset.sum_eq_zero (s := Finset.univ.erase i) fun j hj => by
      rw [← map_sum, sum_inner_off u hu i j (Finset.ne_of_mem_erase hj), map_zero]]
    rw [add_zero]
    have := sum_diag (fun x => ‖u x‖ ^ 2) (d := d) i
    rw [← this]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [@norm_sq_eq_re_inner ℂ]
  rw [Finset.sum_congr rfl fun i _ => this i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ### Variance of a linear statistic of a uniform permutation -/
lemma incl_excl_inner {N : ℕ} (n : Fin N → Fin N → ℂ) (b b' : Fin N) :
    ∑ a, ∑ a' ∈ Finset.univ.erase a, conj (n a b) * n a' b' =
      conj (∑ a, n a b) * (∑ a, n a b') - ∑ a, conj (n a b) * n a b' := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_erase_eq_sub (f := fun a' => conj (n a b) * n a' b')
    (Finset.mem_univ a), Finset.sum_sub_distrib, map_sum, Finset.sum_mul_sum]

lemma incl_excl {N : ℕ} (n : Fin N → Fin N → ℂ) :
    ∑ b, ∑ b' ∈ Finset.univ.erase b, ∑ a, ∑ a' ∈ Finset.univ.erase a, conj (n a b) * n a' b' =
      conj (∑ a, ∑ b, n a b) * (∑ a, ∑ b, n a b) - ∑ a, conj (∑ b, n a b) * (∑ b, n a b) -
        ∑ b, conj (∑ a, n a b) * (∑ a, n a b) + ∑ a, ∑ b, conj (n a b) * n a b := by
  simp only [incl_excl_inner]
  have h1 : ∀ b, ∑ b' ∈ Finset.univ.erase b,
      (conj (∑ a, n a b) * (∑ a, n a b') - ∑ a, conj (n a b) * n a b') =
      (conj (∑ a, n a b) * (∑ a, ∑ b', n a b') - conj (∑ a, n a b) * (∑ a, n a b)) -
        (∑ a, conj (n a b) * (∑ b', n a b') - ∑ a, conj (n a b) * n a b) := by
    intro b
    rw [Finset.sum_erase_eq_sub (f := fun b' => conj (∑ a, n a b) * (∑ a, n a b') -
      ∑ a, conj (n a b) * n a b') (Finset.mem_univ b)]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hs : ∑ i, ∑ a, n a i = ∑ a, ∑ i, n a i := Finset.sum_comm
    have hs2 : ∑ i, ∑ a, conj (n a b) * n a i = ∑ a, conj (n a b) * ∑ i, n a i := by
      rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    rw [hs, hs2]
    ring
  rw [Finset.sum_congr rfl fun b _ => h1 b]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [← map_sum, Finset.sum_comm (f := fun x y => n y x)]
  have h2 : ∑ b, ∑ a, conj (n a b) * ∑ b', n a b' = ∑ a, conj (∑ b, n a b) * ∑ b, n a b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, map_sum]
  rw [h2, Finset.sum_comm (f := fun b a => conj (n a b) * n a b)]
  ring

lemma sum_conj_L_mul_L {N : ℕ} (n : Fin N → Fin N → ℂ) :
    ((N : ℂ) * (N - 1)) * ∑ τ : Equiv.Perm (Fin N),
        conj (∑ b, n (τ b) b) * (∑ b, n (τ b) b) =
      N.factorial * (((N : ℂ) - 1) * ∑ a, ∑ b, conj (n a b) * n a b +
        (conj (∑ a, ∑ b, n a b) * (∑ a, ∑ b, n a b) - ∑ a, conj (∑ b, n a b) * (∑ b, n a b) -
        ∑ b, conj (∑ a, n a b) * (∑ a, n a b) + ∑ a, ∑ b, conj (n a b) * n a b)) := by
  rw [← incl_excl]
  have H : ∀ τ : Equiv.Perm (Fin N), conj (∑ b, n (τ b) b) * (∑ b, n (τ b) b) =
      ∑ b, ∑ b', conj (n (τ b) b) * n (τ b') b' := by
    intro τ; rw [map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun τ _ => H τ]
  have H2 : ∑ τ : Equiv.Perm (Fin N), ∑ b, ∑ b', conj (n (τ b) b) * n (τ b') b' =
      ∑ b, ∑ b', ∑ τ : Equiv.Perm (Fin N), conj (n (τ b) b) * n (τ b') b' := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
  have per : ∀ b, ((N : ℂ) * (N - 1)) *
      ∑ b', ∑ τ : Equiv.Perm (Fin N), conj (n (τ b) b) * n (τ b') b' =
      N.factorial * (((N : ℂ) - 1) * ∑ a, conj (n a b) * n a b) +
        N.factorial * ∑ b' ∈ Finset.univ.erase b, ∑ a, ∑ a' ∈ Finset.univ.erase a,
          conj (n a b) * n a' b' := by
    intro b
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), mul_add]
    congr 1
    · have := sum_perm_one (fun a => conj (n a b) * n a b) b
      rw [mul_comm (N : ℂ) _, mul_assoc, this]; ring
    · rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' hb' => ?_
      exact sum_perm_two (fun u v => conj (n u b) * n v b') b b' (Finset.ne_of_mem_erase hb')
  rw [H2, Finset.mul_sum, Finset.sum_congr rfl fun b _ => per b]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a b => conj (n a b) * n a b)]
  ring

lemma var_identity_C {N : ℕ} (hN : 1 ≤ N) (n : Fin N → Fin N → ℂ) :
    ((N : ℂ) * (N - 1)) * ∑ τ : Equiv.Perm (Fin N),
        conj (∑ b, n (τ b) b - (∑ a, ∑ b, n a b) / N) * (∑ b, n (τ b) b - (∑ a, ∑ b, n a b) / N) =
      N.factorial * (N * ∑ a, ∑ b, conj (n a b) * n a b -
        ∑ a, conj (∑ b, n a b) * (∑ b, n a b) - ∑ b, conj (∑ a, n a b) * (∑ a, n a b) +
        N * (conj ((∑ a, ∑ b, n a b) / N) * ((∑ a, ∑ b, n a b) / N))) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  set s := ∑ a, ∑ b, n a b with hs
  set μ := s / N with hμ
  have hNμ : (N : ℂ) * μ = s := by rw [hμ]; field_simp
  have hB : ∑ τ : Equiv.Perm (Fin N), ∑ b, n (τ b) b = N.factorial * μ := by
    apply mul_left_cancel₀ hN'
    rw [Finset.sum_comm, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun b _ => sum_perm_one (fun a => n a b) b, ← Finset.mul_sum,
      Finset.sum_comm, ← hs, ← hNμ]
    ring
  have hcB : ∑ τ : Equiv.Perm (Fin N), conj (∑ b, n (τ b) b) = N.factorial * conj μ := by
    rw [← map_sum, hB, map_mul, map_natCast]
  have hX : ∑ τ : Equiv.Perm (Fin N), conj (∑ b, n (τ b) b - μ) * (∑ b, n (τ b) b - μ) =
      ∑ τ : Equiv.Perm (Fin N), conj (∑ b, n (τ b) b) * (∑ b, n (τ b) b) -
        N.factorial * (conj μ * μ) := by
    have e : ∀ τ : Equiv.Perm (Fin N), conj (∑ b, n (τ b) b - μ) * (∑ b, n (τ b) b - μ) =
        conj (∑ b, n (τ b) b) * (∑ b, n (τ b) b) - conj μ * (∑ b, n (τ b) b) -
          μ * conj (∑ b, n (τ b) b) + conj μ * μ := by
      intro τ; rw [map_sub]; ring
    rw [Finset.sum_congr rfl fun τ _ => e τ]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hB, hcB,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_perm_C]
    ring
  have hA := sum_conj_L_mul_L n
  rw [hX, mul_sub, hA]
  have hs' : conj s * s = (N : ℂ) ^ 2 * (conj μ * μ) := by
    rw [← hNμ, map_mul, map_natCast]; ring
  rw [hs']
  ring

lemma var_identity {N : ℕ} (hN : 1 ≤ N) (n : Fin N → Fin N → ℂ) :
    ((N : ℝ) * (N - 1)) * ∑ τ : Equiv.Perm (Fin N),
        ‖∑ b, n (τ b) b - (∑ a, ∑ b, n a b) / N‖ ^ 2 =
      N.factorial * (N * ∑ a, ∑ b, ‖n a b‖ ^ 2 - ∑ a, ‖∑ b, n a b‖ ^ 2 -
        ∑ b, ‖∑ a, n a b‖ ^ 2 + N * ‖(∑ a, ∑ b, n a b) / N‖ ^ 2) := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.conj_mul']
  exact var_identity_C hN n

lemma var_bound {N : ℕ} (hN : 2 ≤ N) (n : Fin N → Fin N → ℂ) :
    ∑ τ : Equiv.Perm (Fin N), ‖∑ b, n (τ b) b - (∑ a, ∑ b, n a b) / N‖ ^ 2 ≤
      N.factorial / ((N : ℝ) - 1) * ∑ a, ∑ b, ‖n a b‖ ^ 2 := by
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hid := var_identity (by omega : 1 ≤ N) n
  set s := ∑ a, ∑ b, n a b
  -- Cauchy–Schwarz on the row sums
  have hcs : ‖s‖ ^ 2 ≤ N * ∑ a, ‖∑ b, n a b‖ ^ 2 := by
    have h1 : ‖s‖ ≤ ∑ a, ‖∑ b, n a b‖ := norm_sum_le _ _
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖∑ b, n a b‖)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    calc ‖s‖ ^ 2 ≤ (∑ a, ‖∑ b, n a b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hμ : N * ‖s / N‖ ^ 2 ≤ ∑ a, ‖∑ b, n a b‖ ^ 2 := by
    rw [norm_div, Complex.norm_natCast, div_pow]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hc : 0 ≤ ∑ b, ‖∑ a, n a b‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hF : (0 : ℝ) ≤ N.factorial := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hN1]
  have key : ((N : ℝ) * (N - 1)) * ∑ τ : Equiv.Perm (Fin N), ‖∑ b, n (τ b) b - s / N‖ ^ 2 ≤
      N * (N.factorial * ∑ a, ∑ b, ‖n a b‖ ^ 2) := by
    rw [hid]
    have : N * ∑ a, ∑ b, ‖n a b‖ ^ 2 - ∑ a, ‖∑ b, n a b‖ ^ 2 - ∑ b, ‖∑ a, n a b‖ ^ 2 +
        N * ‖s / N‖ ^ 2 ≤ N * ∑ a, ∑ b, ‖n a b‖ ^ 2 := by linarith
    calc (N.factorial : ℝ) * (N * ∑ a, ∑ b, ‖n a b‖ ^ 2 - ∑ a, ‖∑ b, n a b‖ ^ 2 -
        ∑ b, ‖∑ a, n a b‖ ^ 2 + N * ‖s / N‖ ^ 2)
        ≤ N.factorial * (N * ∑ a, ∑ b, ‖n a b‖ ^ 2) := mul_le_mul_of_nonneg_left this hF
      _ = _ := by ring
  have := le_of_mul_le_mul_left (by rw [← mul_assoc]; exact key :
    (N : ℝ) * ((N - 1) * ∑ τ : Equiv.Perm (Fin N), ‖∑ b, n (τ b) b - s / N‖ ^ 2) ≤
      N * (N.factorial * ∑ a, ∑ b, ‖n a b‖ ^ 2)) hNpos
  linarith

/-! ### `E‖Z x‖²` -/
lemma zx_identity_C {N : ℕ} (y : Fin N → ℂ) (hy : ∑ a, y a = 0) :
    ((N : ℂ) - 1) * ∑ τ : Equiv.Perm (Fin N), ∑ a,
        conj (y (τ.symm a) + y (τ a)) * (y (τ.symm a) + y (τ a)) =
      2 * N * N.factorial * ∑ b, conj (y b) * y b := by
  set Q := ∑ b, conj (y b) * y b
  have hτ : ∀ τ : Equiv.Perm (Fin N), ∑ a,
      conj (y (τ.symm a) + y (τ a)) * (y (τ.symm a) + y (τ a)) =
      2 * Q + ∑ b, conj (y b) * y (τ (τ b)) + ∑ b, conj (y (τ (τ b))) * y b := by
    intro τ
    have e : ∀ a, conj (y (τ.symm a) + y (τ a)) * (y (τ.symm a) + y (τ a)) =
        conj (y (τ.symm a)) * y (τ.symm a) + conj (y (τ a)) * y (τ a) +
          conj (y (τ.symm a)) * y (τ a) + conj (y (τ a)) * y (τ.symm a) := by
      intro a; rw [map_add]; ring
    simp only [e, Finset.sum_add_distrib]
    have h1 : ∑ a, conj (y (τ.symm a)) * y (τ.symm a) = Q :=
      Equiv.sum_comp τ.symm (fun b => conj (y b) * y b)
    have h2 : ∑ a, conj (y (τ a)) * y (τ a) = Q :=
      Equiv.sum_comp τ (fun b => conj (y b) * y b)
    have h3 : ∑ a, conj (y (τ.symm a)) * y (τ a) = ∑ b, conj (y b) * y (τ (τ b)) := by
      rw [← Equiv.sum_comp τ]; simp
    have h4 : ∑ a, conj (y (τ a)) * y (τ.symm a) = ∑ b, conj (y (τ (τ b))) * y b := by
      rw [← Equiv.sum_comp τ]; simp
    rw [h1, h2, h3, h4]; ring
  have hc : ∑ a, conj (y a) = 0 := by rw [← map_sum, hy, map_zero]
  have T1 : ((N : ℂ) - 1) * ∑ b, ∑ τ : Equiv.Perm (Fin N), conj (y b) * y (τ (τ b)) =
      N.factorial * Q := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, mul_left_comm, sum_perm_sq_apply y hy b]; ring
  have T2 : ((N : ℂ) - 1) * ∑ b, ∑ τ : Equiv.Perm (Fin N), conj (y (τ (τ b))) * y b =
      N.factorial * Q := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul, ← mul_assoc, sum_perm_sq_apply (fun a => conj (y a)) hc b]; ring
  have hs1 : ∑ τ : Equiv.Perm (Fin N), ∑ b, conj (y b) * y (τ (τ b)) =
      ∑ b, ∑ τ : Equiv.Perm (Fin N), conj (y b) * y (τ (τ b)) := Finset.sum_comm
  have hs2 : ∑ τ : Equiv.Perm (Fin N), ∑ b, conj (y (τ (τ b))) * y b =
      ∑ b, ∑ τ : Equiv.Perm (Fin N), conj (y (τ (τ b))) * y b := Finset.sum_comm
  have h2Q : ∑ _τ : Equiv.Perm (Fin N), 2 * Q = N.factorial * (2 * Q) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_perm_C]
  rw [Finset.sum_congr rfl fun τ _ => hτ τ, Finset.sum_add_distrib, Finset.sum_add_distrib, hs1,
    hs2, h2Q]
  linear_combination T1 + T2

lemma center_norm_le {N : ℕ} (x : Fin N → ℂ) :
    ∑ b, ‖x b - (∑ a, x a) / N‖ ^ 2 ≤ ∑ b, ‖x b‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast h.ne'
  set c := (∑ a, x a) / N with hc
  have hS : ∑ a, x a = N * c := by rw [hc]; field_simp
  have hC : ∑ b, conj (x b - c) * (x b - c) = ∑ b, conj (x b) * x b - N * (conj c * c) := by
    have e : ∀ b, conj (x b - c) * (x b - c) =
        conj (x b) * x b - conj c * x b - conj (x b) * c + conj c * c := by
      intro b; rw [map_sub]; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, ← map_sum, hS, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, map_mul, map_natCast]
    ring
  have hR : ∑ b, ‖x b - c‖ ^ 2 = ∑ b, ‖x b‖ ^ 2 - N * ‖c‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    simp only [← Complex.conj_mul']
    exact hC
  rw [hR]
  have : 0 ≤ (N : ℝ) * ‖c‖ ^ 2 := by positivity
  linarith

lemma sum_norm_zMat_apply_le {N : ℕ} (hN : 2 ≤ N) (x : EuclideanSpace ℂ (Fin N)) :
    ∑ τ : Equiv.Perm (Fin N), ‖toEuclideanCLM (𝕜 := ℂ) (zMat τ) x‖ ^ 2 ≤
      N.factorial * (2 * N / ((N : ℝ) - 1)) * ‖x‖ ^ 2 := by
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set y : Fin N → ℂ := fun b => x b - (∑ a, x a) / N with hy
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hysum : ∑ a, y a = 0 := by
    simp only [hy, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp; ring
  have hcoord : ∀ τ : Equiv.Perm (Fin N), ‖toEuclideanCLM (𝕜 := ℂ) (zMat τ) x‖ ^ 2 =
      ∑ a, ‖y (τ.symm a) + y (τ a)‖ ^ 2 := by
    intro τ
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [toE_zMat_apply]
    congr 2
    simp only [hy]; ring
  have hid : ((N : ℝ) - 1) * ∑ τ : Equiv.Perm (Fin N), ‖toEuclideanCLM (𝕜 := ℂ) (zMat τ) x‖ ^ 2 =
      2 * N * N.factorial * ∑ b, ‖y b‖ ^ 2 := by
    simp only [hcoord]
    apply Complex.ofReal_injective
    push_cast
    simp only [← Complex.conj_mul']
    exact zx_identity_C y hysum
  have hyx : ∑ b, ‖y b‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; exact center_norm_le (fun b => x b)
  rw [mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ hN1]
  have hF : (0 : ℝ) ≤ N.factorial := by positivity
  calc (∑ τ : Equiv.Perm (Fin N), ‖toEuclideanCLM (𝕜 := ℂ) (zMat τ) x‖ ^ 2) * ((N : ℝ) - 1)
      = 2 * N * N.factorial * ∑ b, ‖y b‖ ^ 2 := by rw [← hid]; ring
    _ ≤ 2 * N * N.factorial * ‖x‖ ^ 2 := by gcongr
    _ = _ := by ring

/-! ### The linear statistic `φ_m(A) = ∑_q conj(A_q) m_q` -/
/-- `φ_m(A) = ∑_q conj(A_q) m_q`. -/
def phi {N : ℕ} (m : Fin N × Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ q, conj (A q.1 q.2) * m q

lemma conj_zMat_entry {N : ℕ} (τ : Equiv.Perm (Fin N)) (a b : Fin N) :
    conj (zMat τ a b) = zMat τ a b := by
  rw [zMat_entry]
  split_ifs <;> simp [map_div₀, map_ofNat (starRingEnd ℂ) 2]

lemma phi_zMat_eq {N : ℕ} (m : Fin N × Fin N → ℂ) (τ : Equiv.Perm (Fin N)) :
    phi m (zMat τ) = ∑ b, (fun a b => m (a, b) + m (b, a)) (τ b) b -
      (∑ a, ∑ b, (fun a b => m (a, b) + m (b, a)) a b) / N := by
  have e : ∀ a b, conj (zMat τ a b) * m (a, b) = (if τ b = a then m (a, b) else 0) +
      (if τ a = b then m (a, b) else 0) - 2 / N * m (a, b) := by
    intro a b
    rw [conj_zMat_entry, zMat_entry]
    split_ifs <;> ring
  have h1 : ∑ a, ∑ b, (if τ b = a then m (a, b) else 0) = ∑ b, m (τ b, b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp
  have h2 : ∑ a, ∑ b, (if τ a = b then m (a, b) else 0) = ∑ a, m (a, τ a) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite_eq]; simp
  have h3 : ∑ a, ∑ b, m (b, a) = ∑ a, ∑ b, m (a, b) := Finset.sum_comm
  simp only [phi, Fintype.sum_prod_type]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3]
  simp only [← Finset.mul_sum]
  ring

lemma sum_phi_zMat_le {N : ℕ} (hN : 2 ≤ N) (m : Fin N × Fin N → ℂ) :
    ∑ τ : Equiv.Perm (Fin N), ‖phi m (zMat τ)‖ ^ 2 ≤
      N.factorial * (4 / ((N : ℝ) - 1)) * ∑ q, ‖m q‖ ^ 2 := by
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hv := var_bound hN (fun a b => m (a, b) + m (b, a))
  have hphi : ∀ τ : Equiv.Perm (Fin N), phi m (zMat τ) =
      ∑ b, (m (τ b, b) + m (b, τ b)) - (∑ a, ∑ b, (m (a, b) + m (b, a))) / N := fun τ =>
    phi_zMat_eq m τ
  simp only [hphi]
  refine hv.trans ?_
  have h2 : ∑ a, ∑ b, ‖m (a, b) + m (b, a)‖ ^ 2 ≤ 4 * ∑ q, ‖m q‖ ^ 2 := by
    have e : ∀ a b, ‖m (a, b) + m (b, a)‖ ^ 2 ≤ 2 * ‖m (a, b)‖ ^ 2 + 2 * ‖m (b, a)‖ ^ 2 := by
      intro a b
      have := norm_add_le (m (a, b)) (m (b, a))
      have h0 := norm_nonneg (m (a, b) + m (b, a))
      nlinarith [sq_nonneg (‖m (a, b)‖ - ‖m (b, a)‖)]
    calc ∑ a, ∑ b, ‖m (a, b) + m (b, a)‖ ^ 2
        ≤ ∑ a, ∑ b, (2 * ‖m (a, b)‖ ^ 2 + 2 * ‖m (b, a)‖ ^ 2) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => e a b
      _ = 2 * ∑ a, ∑ b, ‖m (a, b)‖ ^ 2 + 2 * ∑ a, ∑ b, ‖m (b, a)‖ ^ 2 := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 4 * ∑ q, ‖m q‖ ^ 2 := by
          rw [Finset.sum_comm (f := fun a b => ‖m (b, a)‖ ^ 2), Fintype.sum_prod_type]; ring
  calc (N.factorial : ℝ) / ((N : ℝ) - 1) * ∑ a, ∑ b, ‖m (a, b) + m (b, a)‖ ^ 2
      ≤ N.factorial / ((N : ℝ) - 1) * (4 * ∑ q, ‖m q‖ ^ 2) := by gcongr
    _ = _ := by ring

lemma phi_yMat {d N : ℕ} (m : Fin N × Fin N → ℂ) (σ : Fin d → Equiv.Perm (Fin N)) :
    phi m (yMat σ) = ∑ i, phi m (zMat (σ i)) := by
  simp only [phi, yMat, Matrix.sum_apply, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

lemma sum_phi_zMat {N : ℕ} (hN : 1 ≤ N) (m : Fin N × Fin N → ℂ) :
    ∑ τ : Equiv.Perm (Fin N), phi m (zMat τ) = 0 := by
  simp only [phi]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← map_sum, ← Matrix.sum_apply, sum_zMat hN]
  simp

lemma card_perm_R (N : ℕ) : ((Fintype.card (Equiv.Perm (Fin N)) : ℕ) : ℝ) = (N.factorial : ℝ) := by
  rw [Fintype.card_perm, Fintype.card_fin]

lemma mean_phi_yMat_le {d N : ℕ} (hN : 2 ≤ N) (m : Fin N × Fin N → ℂ) :
    ((Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ))⁻¹ *
        ∑ σ : Fin d → Equiv.Perm (Fin N), ‖phi m (yMat σ)‖ ^ 2 ≤
      4 * d / ((N : ℝ) - 1) * ∑ q, ‖m q‖ ^ 2 := by
  have hK : (0 : ℝ) < Fintype.card (Fin d → Equiv.Perm (Fin N)) := by
    exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hind := sum_norm_sum_sq (d := d) (fun τ : Equiv.Perm (Fin N) => phi m (zMat τ))
    (sum_phi_zMat (by omega) m)
  rw [card_perm_R] at hind
  simp only [phi_yMat]
  have hb := sum_phi_zMat_le hN m
  set K : ℝ := ((Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℕ) : ℝ)
  set S := ∑ σ : Fin d → Equiv.Perm (Fin N), ‖∑ i, phi m (zMat (σ i))‖ ^ 2
  have hS : S = d * K * (∑ τ : Equiv.Perm (Fin N), ‖phi m (zMat τ)‖ ^ 2) / N.factorial := by
    rw [← hind]; field_simp
  rw [hS]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc K⁻¹ * (d * K * (∑ τ : Equiv.Perm (Fin N), ‖phi m (zMat τ)‖ ^ 2) / N.factorial)
      = d * (∑ τ : Equiv.Perm (Fin N), ‖phi m (zMat τ)‖ ^ 2) / N.factorial := by
        field_simp
    _ ≤ d * (N.factorial * (4 / ((N : ℝ) - 1)) * ∑ q, ‖m q‖ ^ 2) / N.factorial := by gcongr
    _ = _ := by field_simp

/-! ### Part M: the variance parameters -/
theorem mean_inner_sq_le {d N : ℕ} (hN : 2 ≤ N) (v w : EuclideanSpace ℂ (Fin N))
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    (∑ σ : Fin d → Equiv.Perm (Fin N), ‖⟪v, toEuclideanCLM (𝕜 := ℂ) (yMat σ) w⟫_ℂ‖ ^ 2) /
      (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≤ 4 * d / (N - 1) := by
  set m : Fin N × Fin N → ℂ := fun q => v q.1 * conj (w q.2) with hm
  have hphi : ∀ σ : Fin d → Equiv.Perm (Fin N),
      ‖⟪v, toEuclideanCLM (𝕜 := ℂ) (yMat σ) w⟫_ℂ‖ = ‖phi m (yMat σ)‖ := by
    intro σ
    rw [← Complex.norm_conj]
    congr 1
    simp only [PiLp.inner_apply, ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, phi, hm,
      Fintype.sum_prod_type, map_sum, map_mul, RCLike.inner_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hmn : ∑ q, ‖m q‖ ^ 2 = 1 := by
    simp only [hm, Fintype.sum_prod_type, norm_mul, Complex.norm_conj, mul_pow, ← Finset.mul_sum,
      ← Finset.sum_mul]
    rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq, hv, hw]; norm_num
  simp only [hphi]
  have := mean_phi_yMat_le (d := d) hN m
  rw [hmn, mul_one] at this
  rw [div_eq_inv_mul]
  exact this

end PartQM
end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
alias mean_inner_sq_le := StrongConv.HighDegUp.PartQM.mean_inner_sq_le

/-- The entry covariance matrix `E[Y_{ab} conj Y_{cd}]` of `Y` (which has mean zero). -/
def covY (d N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ := fun p q =>
  ((Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) : ℂ)⁻¹ *
    ∑ σ : Fin d → Equiv.Perm (Fin N), yMat σ p.1 p.2 * conj (yMat σ q.1 q.2)

end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
namespace PartQM
theorem norm_cov_le {d N : ℕ} (hN : 2 ≤ N) :
    ‖toEuclideanCLM (𝕜 := ℂ) (covY d N)‖ ≤ 4 * d / (N - 1) := by
  have hK : (0 : ℝ) < ((Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℕ) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set K : ℝ := ((Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℕ) : ℝ) with hKdef
  set A := toEuclideanCLM (𝕜 := ℂ) (covY d N)
  let f : (Fin d → Equiv.Perm (Fin N)) → EuclideanSpace ℂ (Fin N × Fin N) → ℂ :=
    fun σ x => phi (fun q => x q) (yMat σ)
  refine opNorm_le_of_gram A f K _ hK (by positivity) (fun x => ?_) (fun x => ?_)
  · -- `‖A x‖² = K⁻¹ ∑ conj (f (A x)) f x`
    have hz : ∀ p, A x p = (K : ℂ)⁻¹ * ∑ σ : Fin d → Equiv.Perm (Fin N),
        yMat σ p.1 p.2 * f σ x := by
      intro p
      simp only [A, f, phi, ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, covY, hKdef,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    have hC : (((‖A x‖ ^ 2 : ℝ)) : ℂ) = (K : ℂ)⁻¹ * ∑ σ : Fin d → Equiv.Perm (Fin N),
        conj (f σ (A x)) * f σ x := by
      rw [EuclideanSpace.norm_sq_eq]
      push_cast
      simp only [← Complex.conj_mul']
      have hf : ∀ σ, conj (f σ (A x)) = ∑ p, yMat σ p.1 p.2 * conj (A x p) := by
        intro σ
        simp only [f, phi, map_sum, map_mul, Complex.conj_conj]
      calc ∑ p, conj (A x p) * A x p
          = ∑ p, conj (A x p) * ((K : ℂ)⁻¹ * ∑ σ : Fin d → Equiv.Perm (Fin N),
              yMat σ p.1 p.2 * f σ x) := Finset.sum_congr rfl fun p _ => by rw [← hz p]
        _ = (K : ℂ)⁻¹ * ∑ σ : Fin d → Equiv.Perm (Fin N),
              (∑ p, yMat σ p.1 p.2 * conj (A x p)) * f σ x := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun p _ => ?_
            ring
        _ = _ := by simp only [hf]
    have h1 : ‖A x‖ ^ 2 = ‖(K : ℂ)⁻¹ * ∑ σ : Fin d → Equiv.Perm (Fin N),
        conj (f σ (A x)) * f σ x‖ := by
      rw [← hC, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h1, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hK.le]
    gcongr
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  · have := mean_phi_yMat_le (d := d) hN (fun q => x q)
    rw [EuclideanSpace.norm_sq_eq]
    convert this using 2

theorem norm_mean_yMat_sq_le {d N : ℕ} (hN : 2 ≤ N) :
    ‖toEuclideanCLM (𝕜 := ℂ)
      (((Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) : ℂ)⁻¹ •
        ∑ σ : Fin d → Equiv.Perm (Fin N), yMat σ * yMat σ)‖ ≤ 2 * d * N / (N - 1) := by
  have hK : (0 : ℝ) < ((Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℕ) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set K : ℝ := ((Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℕ) : ℝ) with hKdef
  let T : (Fin d → Equiv.Perm (Fin N)) → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
    fun σ => toEuclideanCLM (𝕜 := ℂ) (yMat σ)
  have hT : ∀ σ u v, ⟪u, T σ v⟫_ℂ = ⟪T σ u, v⟫_ℂ := by
    intro σ u v
    have hH : (yMat σ)ᴴ = yMat σ := by
      rw [yMat, Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl fun i _ => (zMat_isHermitian (σ i)).eq
    have hs : star (T σ) = T σ := by
      simp only [T]; rw [← map_star, Matrix.star_eq_conjTranspose, hH]
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hs]
  set A := toEuclideanCLM (𝕜 := ℂ)
      (((K : ℝ) : ℂ)⁻¹ • ∑ σ : Fin d → Equiv.Perm (Fin N), yMat σ * yMat σ) with hA
  have hAx : ∀ x, A x = ((K : ℝ) : ℂ)⁻¹ • ∑ σ : Fin d → Equiv.Perm (Fin N), T σ (T σ x) := by
    intro x
    simp only [hA, map_smul, map_sum, map_mul, _root_.smul_apply, _root_.sum_apply,
      mul_apply_eq_comp, T]
  refine opNorm_le_of_gram A (fun σ x => T σ x) K _ hK (by positivity) (fun x => ?_) (fun x => ?_)
  · have h1 : ‖A x‖ ^ 2 = K⁻¹ * ∑ σ : Fin d → Equiv.Perm (Fin N),
        RCLike.re ⟪T σ (A x), T σ x⟫_ℂ := by
      rw [@norm_sq_eq_re_inner ℂ]
      have e : ⟪A x, A x⟫_ℂ = ⟪A x, ((K : ℝ) : ℂ)⁻¹ •
          ∑ σ : Fin d → Equiv.Perm (Fin N), T σ (T σ x)⟫_ℂ := by rw [← hAx]
      rw [e, inner_smul_right, inner_sum,
        Finset.sum_congr rfl fun σ _ => hT σ (A x) (T σ x)]
      rw [← Complex.ofReal_inv]
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul, Complex.re_sum]
    rw [h1]
    gcongr with σ
    exact re_inner_le_norm _ _
  · have hind := sum_norm_sum_sq (d := d)
      (fun τ : Equiv.Perm (Fin N) => toEuclideanCLM (𝕜 := ℂ) (zMat τ) x) (by
        rw [← _root_.sum_apply, ← map_sum, sum_zMat (by omega), map_zero]; rfl)
    rw [card_perm_R] at hind
    have hTx : ∀ σ : Fin d → Equiv.Perm (Fin N),
        T σ x = ∑ i, toEuclideanCLM (𝕜 := ℂ) (zMat (σ i)) x := by
      intro σ; simp only [T, yMat, map_sum, _root_.sum_apply]
    simp only [hTx]
    have hb := sum_norm_zMat_apply_le hN x
    have hF : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
    set S := ∑ σ : Fin d → Equiv.Perm (Fin N), ‖∑ i, toEuclideanCLM (𝕜 := ℂ) (zMat (σ i)) x‖ ^ 2
    have hS : S = d * K * (∑ τ : Equiv.Perm (Fin N),
        ‖toEuclideanCLM (𝕜 := ℂ) (zMat τ) x‖ ^ 2) / N.factorial := by
      rw [← hind]; field_simp
    rw [hS]
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc K⁻¹ * (d * K * (∑ τ : Equiv.Perm (Fin N), ‖toEuclideanCLM (𝕜 := ℂ) (zMat τ) x‖ ^ 2) /
          N.factorial)
        = d * (∑ τ : Equiv.Perm (Fin N), ‖toEuclideanCLM (𝕜 := ℂ) (zMat τ) x‖ ^ 2) /
          N.factorial := by field_simp
      _ ≤ d * (N.factorial * (2 * N / ((N : ℝ) - 1)) * ‖x‖ ^ 2) / N.factorial := by gcongr
      _ = _ := by field_simp

end PartQM
end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
alias norm_mean_yMat_sq_le := StrongConv.HighDegUp.PartQM.norm_mean_yMat_sq_le

alias norm_cov_le := StrongConv.HighDegUp.PartQM.norm_cov_le

end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
namespace PartU
theorem sum_sum_zMat (d N : ℕ) (hN : 1 ≤ N) :
    ∑ ω : Fin d → Equiv.Perm (Fin N), ∑ i, zMat (ω i) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Fintype.sum_equiv (Equiv.piSplitAt i (fun _ => Equiv.Perm (Fin N))) (fun ω => zMat (ω i))
    (fun p => zMat p.1) (fun ω => rfl), Fintype.sum_prod_type_right]
  simp [sum_zMat hN]

theorem stub_apply : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (N d : ℕ), 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
    ∃ σ s v R : ℝ,
      ((Finset.univ.filter fun ω : Fin d → Equiv.Perm (Fin N) =>
        2 * σ + C₀ * (Real.sqrt v * Real.sqrt σ * Real.log N ^ ((3 : ℝ) / 4) +
          s * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
          R * t) < ‖toEuclideanCLM (𝕜 := ℂ) (yMat ω)‖).card : ℝ) /
          (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≤ 4 * N * Real.exp (-t) ∧
      0 ≤ σ ∧ σ ^ 2 ≤ 2 * d * N / (N - 1) ∧ s ≤ Real.sqrt (4 * d / (N - 1)) ∧
      0 ≤ v ∧ v ^ 2 ≤ 4 * d / (N - 1) ∧ 0 ≤ R ∧ R ≤ 4 := by
  obtain ⟨C₀, hC₀, H⟩ := BrailovskayaVanHandel.prob_norm_sum_gt_le
  refine ⟨C₀, hC₀, fun N d hN t ht => ?_⟩
  have h := H N d (Equiv.Perm (Fin N)) (fun _ τ => zMat τ) hN
    (fun _ τ => zMat_isHermitian τ) (fun _ => sum_zMat (by omega)) t ht
  simp only [sum_sum_zMat d N (by omega), smul_zero, sub_zero] at h
  refine ⟨_, _, _, _, h, Real.sqrt_nonneg _, ?_, ?_, Real.sqrt_nonneg _, ?_, ?_, ?_⟩
  · rw [Real.sq_sqrt (norm_nonneg _)]
    exact norm_mean_yMat_sq_le hN
  · refine Real.iSup_le (fun v => Real.iSup_le (fun w => Real.iSup_le (fun hvw =>
      Real.sqrt_le_sqrt (mean_inner_sq_le hN v w hvw.1 hvw.2)) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · rw [Real.sq_sqrt (norm_nonneg _)]
    exact norm_cov_le hN
  · exact Real.iSup_nonneg fun i => Real.iSup_nonneg fun ω => norm_nonneg _
  · exact Real.iSup_le (fun i => Real.iSup_le (fun ω => norm_zMat_le ω) (by norm_num)) (by norm_num)

theorem prob_ge {X : Type*} [Fintype X] [Nonempty X] (E P : X → Prop) [DecidablePred P]
    (h : ∀ x, ¬ P x → E x) :
    1 - ((Finset.univ.filter P).card : ℝ) / Fintype.card X ≤ uniformProb E := by
  classical
  unfold uniformProb
  have hpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  have h2 : (Finset.univ.filter (fun x => ¬ P x)).card ≤ (Finset.univ.filter E).card :=
    Finset.card_le_card (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact h x hx)
  rw [Finset.card_univ] at h1
  rw [one_sub_div hpos.ne', div_le_div_iff_of_pos_right hpos]
  have : ((Fintype.card X : ℕ) : ℝ) - (Finset.univ.filter P).card =
      (Finset.univ.filter (fun x => ¬ P x)).card := by
    rw [← h1]; push_cast; ring
  rw [this]; exact_mod_cast h2

theorem le_of_pow_le {X Y K : ℝ} {n : ℕ} (hn : n ≠ 0) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hK : 1 ≤ K)
    (h : X ^ n ≤ K * Y ^ n) : X ≤ K * Y := by
  have h' : X ^ n ≤ (K * Y) ^ n := h.trans (by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right (le_self_pow₀ hK hn) (pow_nonneg hY n))
  exact (pow_le_pow_iff_left₀ hX (by positivity) hn).1 h'

theorem sq_bound {N d : ℝ} (hNr : 2 ≤ N) (hd0 : 0 ≤ d) :
    2 * d * N / (N - 1) ≤ (Real.sqrt (2 * d) * (1 + 2 / N)) ^ 2 := by
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  rw [mul_pow, Real.sq_sqrt (by positivity), div_le_iff₀ hN1]
  set x := 2 / N with hx
  have hxN : x * N = 2 := by rw [hx]; field_simp
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one (by linarith)]; exact hNr
  have e : (1 + x) ^ 2 * (N - 1) - N = 3 - 2 * x + x ^ 2 * (N - 1) := by
    linear_combination 2 * hxN
  have hpos : 0 ≤ (1 + x) ^ 2 * (N - 1) - N := by
    rw [e]; nlinarith [mul_nonneg (sq_nonneg x) hN1.le]
  nlinarith [mul_nonneg hd0 hpos]

/-- The constant. -/
def Cst (a C₀ : ℝ) : ℝ := 4 + C₀ * (2 + 4 * (a + 3) ^ 2 + 2 * (a + 3) ^ 2 + 2 * (a + 3))

set_option maxHeartbeats 1000000 in
theorem threshold_le (a C₀ : ℝ) (ha : 0 < a) (hC₀ : 0 ≤ C₀) (N d : ℕ) (hN : 2 ≤ N) (hd : 1 ≤ d)
    (t σ s v R : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ (a + 3) * Real.log N)
    (hσ0 : 0 ≤ σ) (hσ : σ ^ 2 ≤ 2 * d * N / (N - 1)) (hs : s ≤ Real.sqrt (4 * d / (N - 1)))
    (hv0 : 0 ≤ v) (hv : v ^ 2 ≤ 4 * d / (N - 1)) (hR0 : 0 ≤ R) (hR : R ≤ 4) :
    2 * σ + C₀ * (Real.sqrt v * Real.sqrt σ * Real.log N ^ ((3 : ℝ) / 4) +
          s * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
          R * t) ≤ (1 + Cst a C₀ * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4) +
          Cst a C₀ * Real.log N ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) +
          Cst a C₀ * Real.log N / (d : ℝ) ^ ((1 : ℝ) / 2)) * (2 * Real.sqrt (2 * d)) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  set L := Real.log N with hLdef
  have hL : 1 / 2 ≤ L := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hNr
    linarith
  have hL0 : 0 ≤ L := by linarith
  set p := L ^ ((3 : ℝ) / 4) with hp
  set q := (N : ℝ) ^ ((1 : ℝ) / 4) with hq
  set r := L ^ ((2 : ℝ) / 3) with hr
  set e := (d : ℝ) ^ ((1 : ℝ) / 6) with he
  set sd := Real.sqrt d with hsd
  have hp0 : 0 ≤ p := Real.rpow_nonneg hL0 _
  have hr0 : 0 ≤ r := Real.rpow_nonneg hL0 _
  have hq0 : 0 < q := by positivity
  have he0 : 0 < e := by positivity
  have hp4 : p ^ 4 = L ^ 3 := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
  have hr3 : r ^ 3 = L ^ 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num
  have hq4 : q ^ 4 = N := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have hd2 : (d : ℝ) ^ ((1 : ℝ) / 2) = sd := (Real.sqrt_eq_rpow _).symm
  have he3 : e ^ 3 = sd := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hsd, Real.sqrt_eq_rpow]; norm_num
  have hsd2 : sd ^ 2 = d := Real.sq_sqrt (by positivity)
  have hsd1 : 1 ≤ sd := by rw [hsd]; exact Real.one_le_sqrt.2 hdr
  have hsd0 : 0 < sd := by linarith
  set A := 2 * Real.sqrt (2 * d) with hAdef
  have hA : 2 * sd ≤ A := by
    rw [hAdef, hsd]; gcongr; linarith
  have hA0 : 0 ≤ A := by positivity
  have hq1 : 1 ≤ q :=
    (pow_le_pow_iff_left₀ (by norm_num) hq0.le (by norm_num : (4 : ℕ) ≠ 0)).1
      (by rw [hq4]; norm_num; linarith)
  have hqN : q ≤ N := by
    have := le_self_pow₀ hq1 (by norm_num : (4 : ℕ) ≠ 0); rw [hq4] at this; exact this
  have hp_half : 1 / 2 ≤ p := by
    refine (pow_le_pow_iff_left₀ (by norm_num) hp0 (by norm_num : (4 : ℕ) ≠ 0)).1 ?_
    rw [hp4]
    have := pow_le_pow_left₀ (by norm_num) hL 3
    nlinarith
  have hσ4 : σ ^ 2 ≤ 4 * d := by
    refine hσ.trans ?_
    rw [div_le_iff₀ hN1]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ d) (by linarith : (0 : ℝ) ≤ N - 2)]
  have hcov : 4 * (d : ℝ) / (N - 1) ≤ 8 * d / N := by
    rw [div_le_div_iff₀ hN1 (by linarith)]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ d) (by linarith : (0 : ℝ) ≤ N - 2)]
  have hinvN : 1 / (N : ℝ) ≤ L := by
    rw [div_le_iff₀ (by linarith)]
    have := mul_le_mul hL hNr (by norm_num) hL0
    norm_num at this ⊢; exact this
  have ht2 : t ^ 2 ≤ ((a + 3) * L) ^ 2 := pow_le_pow_left₀ ht0 ht 2
  have hP1 : 0 ≤ p / q := div_nonneg hp0 hq0.le
  have hP2 : 0 ≤ r / e := div_nonneg hr0 he0.le
  have hP3 : 0 ≤ L / sd := div_nonneg hL0 hsd0.le
  -- term 0
  have h0 : 2 * σ ≤ A + 4 * (p / q) * A := by
    have hNN := sq_bound (N := N) (d := d) hNr (by linarith)
    have hσle : σ ≤ Real.sqrt (2 * d) * (1 + 2 / N) :=
      (pow_le_pow_iff_left₀ hσ0 (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 (hσ.trans hNN)
    have h2N : 2 / (N : ℝ) ≤ 4 * (p / q) := by
      have h1 : 1 / (N : ℝ) ≤ 1 / q := one_div_le_one_div_of_le hq0 hqN
      have h2 : 1 / q ≤ 2 * p / q := div_le_div_of_nonneg_right (by linarith) hq0.le
      have : 2 / (N : ℝ) = 2 * (1 / N) := by ring
      rw [this, mul_div_assoc] at *
      linarith
    calc 2 * σ ≤ 2 * (Real.sqrt (2 * d) * (1 + 2 / N)) := by linarith
      _ ≤ 2 * (Real.sqrt (2 * d) * (1 + 4 * (p / q))) := by gcongr
      _ = A + 4 * (p / q) * A := by rw [hAdef]; ring
  -- term 1
  have h1 : Real.sqrt v * Real.sqrt σ * p ≤ 2 * (p / q) * A := by
    have hX : Real.sqrt v * Real.sqrt σ ≤ 1 * (4 * sd / q) := by
      refine le_of_pow_le (n := 4) (by norm_num) (by positivity) (by positivity) le_rfl ?_
      have e1 : (Real.sqrt v * Real.sqrt σ) ^ 4 = v ^ 2 * σ ^ 2 := by
        rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, Real.sq_sqrt hv0,
          Real.sq_sqrt hσ0]
      have e2 : (4 * sd / q) ^ 4 = 256 * (sd ^ 2) ^ 2 / q ^ 4 := by ring
      rw [e1, one_mul, e2, hsd2, hq4]
      calc v ^ 2 * σ ^ 2 ≤ (4 * d / (N - 1)) * (4 * d) :=
            mul_le_mul hv hσ4 (by positivity) (by positivity)
        _ ≤ 256 * (d : ℝ) ^ 2 / N := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ hN1 (by linarith)]; nlinarith
    calc Real.sqrt v * Real.sqrt σ * p ≤ 1 * (4 * sd / q) * p := by gcongr
      _ = 2 * (p / q) * (2 * sd) := by ring
      _ ≤ 2 * (p / q) * A := by gcongr
  -- term 2
  have h2 : s * Real.sqrt t ≤ (4 * (a + 3) ^ 2) * (p / q) * A := by
    have hX : Real.sqrt (4 * d / (N - 1)) * Real.sqrt t ≤
        (4 * (a + 3) ^ 2) * ((p / q) * (2 * sd)) := by
      refine le_of_pow_le (n := 4) (by norm_num) (by positivity) (by positivity) (by nlinarith) ?_
      have e1 : (Real.sqrt (4 * d / (N - 1)) * Real.sqrt t) ^ 4 =
          (4 * d / (N - 1)) ^ 2 * t ^ 2 := by
        rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, Real.sq_sqrt (by positivity),
          Real.sq_sqrt ht0]
      have e2 : ((p / q) * (2 * sd)) ^ 4 = p ^ 4 / q ^ 4 * 16 * (sd ^ 2) ^ 2 := by ring
      rw [e1, e2, hp4, hq4, hsd2]
      calc (4 * d / (N - 1)) ^ 2 * t ^ 2 ≤ (8 * d / N) ^ 2 * ((a + 3) * L) ^ 2 := by
            gcongr
        _ = 64 * (a + 3) ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * (1 / N) * (1 / N) := by ring
        _ ≤ 64 * (a + 3) ^ 2 * (d : ℝ) ^ 2 * L ^ 2 * L * (1 / N) := by gcongr
        _ = 4 * (a + 3) ^ 2 * (L ^ 3 / N * 16 * (d : ℝ) ^ 2) := by ring
    calc s * Real.sqrt t ≤ Real.sqrt (4 * d / (N - 1)) * Real.sqrt t := by gcongr
      _ ≤ (4 * (a + 3) ^ 2) * ((p / q) * (2 * sd)) := hX
      _ ≤ (4 * (a + 3) ^ 2) * ((p / q) * A) := by gcongr
      _ = (4 * (a + 3) ^ 2) * (p / q) * A := by ring
  -- term 3
  have h3 : R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) ≤
      (2 * (a + 3) ^ 2) * (r / e) * A := by
    have hX : R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) ≤
        (2 * (a + 3) ^ 2) * ((r / e) * (2 * sd)) := by
      refine le_of_pow_le (n := 3) (by norm_num) (by positivity) (by positivity) (by nlinarith) ?_
      have e1 : (R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3)) ^ 3 =
          R * σ ^ 2 * t ^ 2 := by
        rw [mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (σ ^ ((2 : ℝ) / 3)),
          ← Real.rpow_natCast (t ^ ((2 : ℝ) / 3)), ← Real.rpow_mul hR0, ← Real.rpow_mul hσ0,
          ← Real.rpow_mul ht0]
        norm_num
      have e2 : ((r / e) * (2 * sd)) ^ 3 = r ^ 3 / e ^ 3 * 8 * sd ^ 3 := by ring
      rw [e1, e2, hr3, he3]
      have e3 : L ^ 2 / sd * 8 * sd ^ 3 = 8 * L ^ 2 * sd ^ 2 := by field_simp
      rw [e3, hsd2]
      calc R * σ ^ 2 * t ^ 2 ≤ 4 * (4 * d) * ((a + 3) * L) ^ 2 := by gcongr
        _ = 2 * (a + 3) ^ 2 * (8 * L ^ 2 * d) := by ring
    calc _ ≤ (2 * (a + 3) ^ 2) * ((r / e) * (2 * sd)) := hX
      _ ≤ (2 * (a + 3) ^ 2) * ((r / e) * A) := by gcongr
      _ = _ := by ring
  -- term 4
  have h4 : R * t ≤ (2 * (a + 3)) * (L / sd) * A := by
    calc R * t ≤ 4 * ((a + 3) * L) := by gcongr
      _ = (2 * (a + 3)) * (L / sd) * (2 * sd) := by field_simp; ring
      _ ≤ (2 * (a + 3)) * (L / sd) * A := by gcongr
  -- combine
  rw [hd2, mul_div_assoc, mul_div_assoc, mul_div_assoc]
  have hsum := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) hC₀
  have key : (1 + Cst a C₀ * (p / q) + Cst a C₀ * (r / e) + Cst a C₀ * (L / sd)) * A =
      A + 4 * (p / q) * A + C₀ * (2 * (p / q) * A + 4 * (a + 3) ^ 2 * (p / q) * A +
        2 * (a + 3) ^ 2 * (r / e) * A + 2 * (a + 3) * (L / sd) * A) +
      C₀ * ((2 * (a + 3) ^ 2 + 2 * (a + 3)) * (p / q) * A +
        (2 + 4 * (a + 3) ^ 2 + 2 * (a + 3)) * (r / e) * A +
        (2 + 4 * (a + 3) ^ 2 + 2 * (a + 3) ^ 2) * (L / sd) * A) +
      4 * (r / e) * A + 4 * (L / sd) * A := by
    simp only [Cst]; ring
  have hextra : 0 ≤ C₀ * ((2 * (a + 3) ^ 2 + 2 * (a + 3)) * (p / q) * A +
        (2 + 4 * (a + 3) ^ 2 + 2 * (a + 3)) * (r / e) * A +
        (2 + 4 * (a + 3) ^ 2 + 2 * (a + 3) ^ 2) * (L / sd) * A) := by
    have : 0 ≤ a + 3 := by linarith
    positivity
  have hx2 : 0 ≤ 4 * (r / e) * A := by positivity
  have hx3 : 0 ≤ 4 * (L / sd) * A := by positivity
  rw [key]
  linarith

theorem prob_ge' {X : Type*} [Fintype X] [Nonempty X] (E P : X → Prop) [DecidablePred P]
    (h : ∀ x, ¬ P x → E x) (c : ℝ)
    (hc : ((Finset.univ.filter P).card : ℝ) / Fintype.card X ≤ c) : 1 - c ≤ uniformProb E :=
  le_trans (by linarith) (prob_ge E P h)

theorem prob_norm_adjPerp_le_highDegree_ge_dev (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d →
      1 - (N : ℝ) ^ (-a) ≤ uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ‖adjPerp σ‖ ≤ (1 + C * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4) +
          C * Real.log N ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) +
          C * Real.log N / (d : ℝ) ^ ((1 : ℝ) / 2)) * (2 * Real.sqrt (2 * d))) := by
  obtain ⟨C₀, hC₀, H⟩ := stub_apply
  refine ⟨Cst a C₀, by unfold Cst; positivity, fun N d hN hd => ?_⟩
  rcases (show N = 1 ∨ 2 ≤ N by omega) with rfl | hN2
  · simp only [Nat.cast_one, Real.one_rpow, sub_self]
    unfold uniformProb
    positivity
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  set t := (a + 1) * Real.log N + Real.log 4 with htdef
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ Real.log N := by linarith
  have ht0 : 0 ≤ t := by
    rw [htdef, hlog4]; have := mul_nonneg (by linarith : (0 : ℝ) ≤ a + 1) hL; linarith
  have ht : t ≤ (a + 3) * Real.log N := by
    rw [htdef, hlog4]; nlinarith
  have hexp : 4 * (N : ℝ) * Real.exp (-t) = (N : ℝ) ^ (-a) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    have h4 : (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
    have hNe : (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log (by linarith)).symm
    calc 4 * (N : ℝ) * Real.exp (-t)
        = Real.exp (Real.log 4) * Real.exp (Real.log N) * Real.exp (-t) := by
          rw [← h4, ← hNe]
      _ = Real.exp (Real.log N * -a) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [htdef]; ring
  obtain ⟨σ, s, v, R, hP, hσ0, hσ, hs, hv0, hv, hR0, hR⟩ := H N d hN2 t ht0
  have hT := threshold_le a C₀ ha hC₀.le N d hN2 hd t σ s v R ht0 ht hσ0 hσ hs hv0 hv hR0 hR
  rw [← hexp]
  refine prob_ge' _ _ ?_ _ hP
  intro ω hω
  rw [not_lt, norm_yMat_eq hN] at hω
  exact hω.trans hT

end PartU
end StrongConv.HighDegUp
end
end

section
noncomputable section
open Matrix ComplexConjugate Filter
open scoped InnerProductSpace
namespace StrongConv.HighDegUp
/-! ## Part U: assembly -/
alias prob_norm_adjPerp_le_highDegree_ge_dev := StrongConv.HighDegUp.PartU.prob_norm_adjPerp_le_highDegree_ge_dev

end StrongConv.HighDegUp
end
end

theorem solution (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ N d : ℕ, 1 ≤ N → 1 ≤ d →
      1 - (N : ℝ) ^ (-a) ≤ StrongConv.uniformProb (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ‖StrongConv.adjPerp σ‖ ≤ (1 + C * Real.log N ^ ((3 : ℝ) / 4) / (N : ℝ) ^ ((1 : ℝ) / 4) +
          C * Real.log N ^ ((2 : ℝ) / 3) / (d : ℝ) ^ ((1 : ℝ) / 6) +
          C * Real.log N / (d : ℝ) ^ ((1 : ℝ) / 2)) * (2 * Real.sqrt (2 * d))) :=
  StrongConv.HighDegUp.prob_norm_adjPerp_le_highDegree_ge_dev a ha
