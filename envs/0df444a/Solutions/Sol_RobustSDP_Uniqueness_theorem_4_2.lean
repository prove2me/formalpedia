-- Prove2me | solution 1 for RobustSDP.Uniqueness.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-05T06:18:20.260628+00:00
-- url     : https://prove2.me/submissions/27a4dd80-51e4-4246-aa7c-f87c9ff9e124

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

set_option autoImplicit false


/- Inlined checked module: SymmetricCone -/
section
open Matrix Filter Topology

namespace RobustSDP.Proof

abbrev SymMat (I : Type*) := ↥(selfAdjoint.submodule ℝ (Matrix I I ℝ))

variable {I : Type*}

theorem symMat_isHermitian (M : SymMat I) : (M : Matrix I I ℝ).IsHermitian := M.property

def symMatOf (M : Matrix I I ℝ) (hM : M.IsHermitian) : SymMat I := ⟨M, hM⟩

variable [Fintype I]

def matrixQuad (M : Matrix I I ℝ) (v : I → ℝ) : ℝ := v ⬝ᵥ (M *ᵥ v)

theorem matrixQuad_smul (M : Matrix I I ℝ) (a : ℝ) (v : I → ℝ) :
    matrixQuad M (a • v) = a ^ 2 * matrixQuad M v := by
  simp only [matrixQuad, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem continuous_matrixQuad :
    Continuous (fun z : SymMat I × (I → ℝ) => matrixQuad (z.1 : Matrix I I ℝ) z.2) := by
  change Continuous (fun z : SymMat I × (I → ℝ) =>
    ∑ i, z.2 i * ∑ j, (z.1 : Matrix I I ℝ) i j * z.2 j)
  refine continuous_finsetSum _ (fun i _ => ?_)
  refine ((continuous_apply i).comp continuous_snd).mul ?_
  refine continuous_finsetSum _ (fun j _ => ?_)
  have hM : Continuous (fun z : SymMat I × (I → ℝ) => (z.1 : Matrix I I ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hEntry : Continuous (fun z : SymMat I × (I → ℝ) => (z.1 : Matrix I I ℝ) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hM)
  exact hEntry.mul ((continuous_apply j).comp continuous_snd)

theorem posDef_iff_norm_one (M : SymMat I) :
    (M : Matrix I I ℝ).PosDef ↔ ∀ v : I → ℝ, ‖v‖ = 1 → 0 < matrixQuad M v := by
  constructor
  · intro hM v hv
    have hne : v ≠ 0 := by
      intro hz
      subst v
      norm_num at hv
    simpa only [matrixQuad, star_trivial] using hM.dotProduct_mulVec_pos hne
  · intro hM
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (symMat_isHermitian M)
    intro v hv
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : I → ℝ := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by
      dsimp [w]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have hp := hM w hw
    have he : matrixQuad M w = (‖v‖⁻¹) ^ 2 * matrixQuad M v := by
      exact matrixQuad_smul (M : Matrix I I ℝ) (‖v‖⁻¹) v
    rw [he] at hp
    have hpos : 0 < matrixQuad M v :=
      (mul_pos_iff_of_pos_left (sq_pos_of_pos (inv_pos.mpr hn))).mp hp
    simpa only [matrixQuad, star_trivial] using hpos

theorem isOpen_posDef : IsOpen {M : SymMat I | (M : Matrix I I ℝ).PosDef} := by
  apply isOpen_iff_mem_nhds.mpr
  intro M hM
  have hK : IsCompact (Metric.sphere (0 : I → ℝ) 1) := isCompact_sphere _ _
  have hU : IsOpen {z : SymMat I × (I → ℝ) | 0 < matrixQuad (z.1 : Matrix I I ℝ) z.2} :=
    isOpen_lt continuous_const continuous_matrixQuad
  have hev : ∀ᶠ B : SymMat I in 𝓝 M,
      ∀ v ∈ Metric.sphere (0 : I → ℝ) 1, 0 < matrixQuad B v := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hn : ‖v‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hv
    exact hU.mem_nhds ((posDef_iff_norm_one M).mp hM v hn)
  change ∀ᶠ B : SymMat I in 𝓝 M, (B : Matrix I I ℝ).PosDef
  filter_upwards [hev] with B hB
  apply (posDef_iff_norm_one B).mpr
  intro v hv
  exact hB v (by simpa only [Metric.mem_sphere, dist_zero_right] using hv)

omit [Fintype I] in
theorem convex_posDef : Convex ℝ {M : SymMat I | (M : Matrix I I ℝ).PosDef} := by
  intro A hA B hB a b ha hb hab
  change (A : Matrix I I ℝ).PosDef at hA
  change (B : Matrix I I ℝ).PosDef at hB
  change (a • (A : Matrix I I ℝ) + b • (B : Matrix I I ℝ)).PosDef
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    subst b
    simpa only [zero_smul, one_smul, zero_add] using hB
  · exact (hA.smul (lt_of_le_of_ne ha (Ne.symm ha0))).add_posSemidef (hB.posSemidef.smul hb)

omit [Fintype I] in
theorem convex_posSemidef : Convex ℝ {M : SymMat I | (M : Matrix I I ℝ).PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

end RobustSDP.Proof
end


/- Inlined checked module: SymmetricDual -/
section
open Matrix

noncomputable section

namespace RobustSDP.Proof

variable {I : Type*}

def symmetrize : Matrix I I ℝ →ₗ[ℝ] SymMat I where
  toFun M := ⟨(1 / 2 : ℝ) • (M + Mᵀ), by
    change ((1 / 2 : ℝ) • (M + Mᵀ)).IsHermitian
    rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    change (1 / 2 : ℝ) * (M j i + M i j) = (1 / 2 : ℝ) * (M i j + M j i)
    ring⟩
  map_add' M N := by
    apply Subtype.ext
    ext i j
    change (1 / 2 : ℝ) * ((M i j + N i j) + (M j i + N j i)) =
      (1 / 2 : ℝ) * (M i j + M j i) + (1 / 2 : ℝ) * (N i j + N j i)
    ring
  map_smul' a M := by
    apply Subtype.ext
    ext i j
    change (1 / 2 : ℝ) * (a * M i j + a * M j i) = a * ((1 / 2 : ℝ) * (M i j + M j i))
    ring

theorem symmetrize_transpose (M : Matrix I I ℝ) : symmetrize Mᵀ = symmetrize M := by
  apply Subtype.ext
  change (1 / 2 : ℝ) • (Mᵀ + Mᵀᵀ) = (1 / 2 : ℝ) • (M + Mᵀ)
  rw [Matrix.transpose_transpose, add_comm]

theorem symmetrize_coe (M : SymMat I) : symmetrize (M : Matrix I I ℝ) = M := by
  apply Subtype.ext
  have hM : (M : Matrix I I ℝ)ᵀ = M := Matrix.isHermitian_iff_isSymm.mp (symMat_isHermitian M)
  change (1 / 2 : ℝ) • ((M : Matrix I I ℝ) + (M : Matrix I I ℝ)ᵀ) = M
  rw [hM]
  ext i j
  change (1 / 2 : ℝ) * ((M : Matrix I I ℝ) i j + (M : Matrix I I ℝ) i j) = (M : Matrix I I ℝ) i j
  ring

variable [DecidableEq I]

def dualMatrix (f : SymMat I →ₗ[ℝ] ℝ) : Matrix I I ℝ :=
  fun i j => f (symmetrize (Matrix.single j i 1))

theorem dualMatrix_isHermitian (f : SymMat I →ₗ[ℝ] ℝ) : (dualMatrix f).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  change f (symmetrize (Matrix.single i j 1)) = f (symmetrize (Matrix.single j i 1))
  rw [← Matrix.transpose_single i j (1 : ℝ), symmetrize_transpose]

variable [Fintype I]

theorem trace_dualMatrix (f : SymMat I →ₗ[ℝ] ℝ) (M : SymMat I) :
    (dualMatrix f * (M : Matrix I I ℝ)).trace = f M := by
  have hM : (M : Matrix I I ℝ) =
      ∑ i, ∑ j, (M : Matrix I I ℝ) i j • Matrix.single i j (1 : ℝ) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single (M : Matrix I I ℝ)
  have hrep : f M = ∑ i, ∑ j, (M : Matrix I I ℝ) i j * f (symmetrize (Matrix.single i j 1)) := by
    calc
      f M = f (symmetrize (M : Matrix I I ℝ)) := congrArg f (symmetrize_coe M).symm
      _ = f (symmetrize (∑ i, ∑ j, (M : Matrix I I ℝ) i j • Matrix.single i j (1 : ℝ))) :=
        congrArg (fun A => f (symmetrize A)) hM
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
  change (∑ i, ∑ j, f (symmetrize (Matrix.single j i 1)) * (M : Matrix I I ℝ) j i) = f M
  rw [Finset.sum_comm]
  simpa only [mul_comm] using hrep.symm

theorem dualMatrix_posSemidef (f : SymMat I →ₗ[ℝ] ℝ)
    (hf : ∀ M : SymMat I, (M : Matrix I I ℝ).PosSemidef → 0 ≤ f M) :
    (dualMatrix f).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (dualMatrix_isHermitian f)
  intro v
  have hv : (Matrix.vecMulVec v v).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_star_self v
  let M : SymMat I := symMatOf (Matrix.vecMulVec v v) hv.isHermitian
  have hpos := hf M hv
  rw [← trace_dualMatrix f M] at hpos
  change 0 ≤ (dualMatrix f * Matrix.vecMulVec v v).trace at hpos
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at hpos
  simpa only [star_trivial] using hpos

end RobustSDP.Proof
end
end


/- Inlined checked module: SlaterSeparation -/
section
open Matrix Filter Topology

namespace RobustSDP.Proof

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]

def slaterSet (A0 : SymMat I) (A : E →ₗ[ℝ] SymMat I) (c : E →ₗ[ℝ] ℝ)
    (v : ℝ) : Set (ℝ × SymMat I) :=
  {z | ∃ y, c y - v < z.1 ∧ ((A0 + A y - z.2 : SymMat I) : Matrix I I ℝ).PosDef}

theorem slaterSet_open (A0 : SymMat I) (A : E →ₗ[ℝ] SymMat I)
    (c : E →ₗ[ℝ] ℝ) (v : ℝ) : IsOpen (slaterSet A0 A c v) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨y, hyr, hyB⟩
  have h₁ : IsOpen {w : ℝ × SymMat I | c y - v < w.1} :=
    isOpen_lt continuous_const continuous_fst
  have h₂ : IsOpen {w : ℝ × SymMat I |
      ((A0 + A y - w.2 : SymMat I) : Matrix I I ℝ).PosDef} :=
    isOpen_posDef.preimage (continuous_const.sub continuous_snd)
  filter_upwards [h₁.mem_nhds hyr, h₂.mem_nhds hyB] with w hw₁ hw₂
  exact ⟨y, hw₁, hw₂⟩

omit [Fintype I] in
theorem slaterSet_convex (A0 : SymMat I) (A : E →ₗ[ℝ] SymMat I)
    (c : E →ₗ[ℝ] ℝ) (v : ℝ) : Convex ℝ (slaterSet A0 A c v) := by
  rintro z ⟨x, hxr, hxB⟩ w ⟨y, hyr, hyB⟩ a b ha hb hab
  refine ⟨a • x + b • y, ?_, ?_⟩
  · change c (a • x + b • y) - v < a * z.1 + b * w.1
    simp only [map_add, map_smul, smul_eq_mul]
    by_cases ha0 : a = 0
    · subst a
      have hb1 : b = 1 := by linarith
      simpa only [hb1, zero_mul, one_mul, zero_add] using hyr
    · have hx := mul_lt_mul_of_pos_left hxr (lt_of_le_of_ne ha (Ne.symm ha0))
      have hy := mul_le_mul_of_nonneg_left hyr.le hb
      have hv : a * v + b * v = v := by
        calc
          _ = (a + b) * v := by ring
          _ = v := by rw [hab, one_mul]
      nlinarith
  · have he : A0 + A (a • x + b • y) - (a • z + b • w).2 =
        a • (A0 + A x - z.2) + b • (A0 + A y - w.2) := by
      change A0 + A (a • x + b • y) - (a • z.2 + b • w.2) = _
      simp only [map_add, map_smul]
      calc
        _ = (a + b) • A0 + (a • A x + b • A y) - (a • z.2 + b • w.2) := by
          rw [hab, one_smul]
        _ = _ := by module
    rw [he]
    exact convex_posDef hxB hyB ha hb hab

omit [Fintype I] in
theorem slaterSet_zero_not_mem (A0 : SymMat I) (A : E →ₗ[ℝ] SymMat I)
    (c : E →ₗ[ℝ] ℝ) (ystar : E)
    (hopt : ∀ y, ((A0 + A y : SymMat I) : Matrix I I ℝ).PosSemidef → c ystar ≤ c y) :
    (0 : ℝ × SymMat I) ∉ slaterSet A0 A c (c ystar) := by
  rintro ⟨y, hyr, hyB⟩
  have hy : ((A0 + A y : SymMat I) : Matrix I I ℝ).PosDef := by
    simpa using hyB
  have := hopt y hy.posSemidef
  change c y - c ystar < 0 at hyr
  linarith

end RobustSDP.Proof
end


/- Inlined checked module: AffineSlater -/
section
open Matrix Filter Topology

noncomputable section

namespace RobustSDP.Proof

variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I] [DecidableEq I]

theorem affine_slater_functional (A0 : SymMat I) (A : E →ₗ[ℝ] SymMat I)
    (c : E →ₗ[ℝ] ℝ) (ystar : E)
    (hstar : ((A0 + A ystar : SymMat I) : Matrix I I ℝ).PosSemidef)
    (hopt : ∀ y, ((A0 + A y : SymMat I) : Matrix I I ℝ).PosSemidef → c ystar ≤ c y)
    (hslater : ∃ y, ((A0 + A y : SymMat I) : Matrix I I ℝ).PosDef) :
    ∃ (L : SymMat I →ₗ[ℝ] ℝ) (lam : ℝ), 0 < lam ∧
      (∀ P : SymMat I, (P : Matrix I I ℝ).PosSemidef → 0 ≤ L P) ∧
      ∀ y, L (A0 + A y) = lam * (c y - c ystar) := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point
    (slaterSet_convex A0 A c (c ystar)) (slaterSet_open A0 A c (c ystar))
    (slaterSet_zero_not_mem A0 A c ystar hopt)
  let a : ℝ := f (1, 0)
  let L : SymMat I →ₗ[ℝ] ℝ :=
    f.toLinearMap.comp (LinearMap.inr ℝ ℝ (SymMat I))
  have heval (r : ℝ) (B : SymMat I) : f (r, B) = a * r + L B := by
    have hp : (r, B) = r • (1, (0 : SymMat I)) + (0, B) := by ext <;> simp
    rw [hp, map_add, map_smul]
    change r * a + L B = a * r + L B
    ring
  have hsep (r : ℝ) (B : SymMat I) (h : (r, B) ∈ slaterSet A0 A c (c ystar)) :
      a * r + L B < 0 := by
    have hh := hf (r, B) h
    rw [map_zero, heval] at hh
    exact hh
  obtain ⟨ys, hys⟩ := hslater
  let r : ℝ := max (c ys - c ystar) 0 + 1
  have hr : 0 < r := by dsimp [r]; linarith [le_max_right (c ys - c ystar) 0]
  have hrc : c ys - c ystar < r := by dsimp [r]; linarith [le_max_left (c ys - c ystar) 0]
  have ha : a < 0 := by
    have hh := hsep r 0 ⟨ys, hrc, by simpa using hys⟩
    simp only [map_zero, add_zero] at hh
    nlinarith
  have hL (P : SymMat I) (hP : (P : Matrix I I ℝ).PosSemidef) : 0 ≤ L P := by
    by_contra h
    have hn : 0 < -L P := neg_pos.mpr (lt_of_not_ge h)
    obtain ⟨t, ht, hlarge⟩ := exists_pos_lt_mul hn (-(a * r))
    have hm : (r, -(t • P)) ∈ slaterSet A0 A c (c ystar) := by
      refine ⟨ys, hrc, ?_⟩
      change ((A0 + A ys : SymMat I) - -(t • P) : SymMat I).val.PosDef
      simpa only [sub_neg_eq_add, Submodule.coe_add, Submodule.coe_smul] using
        hys.add_posSemidef (hP.smul ht.le)
    have hh := hsep r (-(t • P)) hm
    simp only [map_neg, map_smul, smul_eq_mul] at hh
    nlinarith
  let J : SymMat I := symMatOf (1 : Matrix I I ℝ) Matrix.isHermitian_one
  have hbound (y : E) : L (A0 + A y) ≤ (-a) * (c y - c ystar) := by
    have happ (d : ℝ) (hd : 0 < d) :
        L (A0 + A y) < (-a) * (c y - c ystar) + d * ((-a) + L J) := by
      have hm : (c y - c ystar + d, A0 + A y - d • J) ∈
          slaterSet A0 A c (c ystar) := by
        refine ⟨y, by linarith, ?_⟩
        have he : A0 + A y - (A0 + A y - d • J) = d • J := by abel
        rw [he]
        exact Matrix.PosDef.one.smul hd
      have hh := hsep _ _ hm
      simp only [map_sub, map_smul, smul_eq_mul] at hh
      nlinarith
    by_contra h
    have hg : 0 < L (A0 + A y) - (-a) * (c y - c ystar) := sub_pos.mpr (lt_of_not_ge h)
    obtain ⟨d, hd, hsmall⟩ := exists_pos_mul_lt hg ((-a) + L J)
    have := happ d hd
    nlinarith
  have hzero : L (A0 + A ystar) = 0 := by
    have hupper := hbound ystar
    have hlower := hL (A0 + A ystar) hstar
    simp only [sub_self, mul_zero] at hupper
    exact le_antisymm hupper hlower
  refine ⟨L, -a, neg_pos.mpr ha, hL, ?_⟩
  intro y
  apply le_antisymm (hbound y)
  have hh := hbound (ystar + ystar - y)
  simp only [map_add, map_sub] at hh hzero ⊢
  nlinarith

theorem affine_slater_multiplier (A0 : SymMat I) (A : E →ₗ[ℝ] SymMat I)
    (c : E →ₗ[ℝ] ℝ) (ystar : E)
    (hstar : ((A0 + A ystar : SymMat I) : Matrix I I ℝ).PosSemidef)
    (hopt : ∀ y, ((A0 + A y : SymMat I) : Matrix I I ℝ).PosSemidef → c ystar ≤ c y)
    (hslater : ∃ y, ((A0 + A y : SymMat I) : Matrix I I ℝ).PosDef) :
    ∃ W : Matrix I I ℝ, W.PosSemidef ∧
      ∀ y, (W * (A0 + A y : SymMat I)).trace = c y - c ystar := by
  obtain ⟨L, lam, hlam, hL, he⟩ := affine_slater_functional A0 A c ystar hstar hopt hslater
  let g : SymMat I →ₗ[ℝ] ℝ := lam⁻¹ • L
  refine ⟨dualMatrix g, dualMatrix_posSemidef g ?_, ?_⟩
  · intro P hP
    exact mul_nonneg (inv_nonneg.mpr hlam.le) (hL P hP)
  · intro y
    rw [trace_dualMatrix]
    change lam⁻¹ * L (A0 + A y) = _
    rw [he, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]

end RobustSDP.Proof
end
end


/- Inlined checked module: OptimalExistence -/
section
open Matrix

namespace RobustSDP.Proof

variable {m n p q : ℕ} (D : RobustSDP.Uniqueness.SDPData m n p q)

theorem lmi_isHermitian (hsym : D.Symmetric) (x : Fin m → ℝ) (t : ℝ) :
    (D.lmi x t).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  change (D.lmi x t)ᵀ = D.lmi x t
  have hF : (D.F x)ᵀ = D.F x := by
    simp only [RobustSDP.Uniqueness.SDPData.F, Matrix.transpose_add, Matrix.transpose_sum,
      Matrix.transpose_smul, hsym.1.eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [(hsym.2 i).eq]
  simp only [RobustSDP.Uniqueness.SDPData.lmi, Matrix.fromBlocks_transpose,
    Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_one, hF]

theorem continuous_lmi : Continuous (fun y : (Fin m → ℝ) × ℝ => D.lmi y.1 y.2) := by
  have hF : Continuous (fun y : (Fin m → ℝ) × ℝ => D.F y.1) := by
    unfold RobustSDP.Uniqueness.SDPData.F
    exact continuous_const.add (continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp continuous_fst).smul continuous_const))
  have hR : Continuous (fun y : (Fin m → ℝ) × ℝ => D.R y.1) := by
    unfold RobustSDP.Uniqueness.SDPData.R
    exact continuous_const.add (continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp continuous_fst).smul continuous_const))
  exact (hF.sub (continuous_snd.smul continuous_const)).matrix_fromBlocks
    hR.matrix_transpose hR (continuous_snd.smul continuous_const)

theorem continuous_objective (c : Fin m → ℝ) :
    Continuous (fun y : (Fin m → ℝ) × ℝ => c ⬝ᵥ y.1) := by
  exact continuous_const.dotProduct continuous_fst

theorem isClosed_feasible (hsym : D.Symmetric) :
    IsClosed {y : (Fin m → ℝ) × ℝ | D.Feasible y} := by
  have he : {y : (Fin m → ℝ) × ℝ | D.Feasible y} =
      ⋂ v : (Fin n ⊕ Fin q) → ℝ, {y | 0 ≤ v ⬝ᵥ (D.lmi y.1 y.2 *ᵥ v)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hy v
      simpa only [star_trivial] using hy.dotProduct_mulVec_nonneg v
    · intro hy
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (lmi_isHermitian D hsym _ _)
      simpa only [star_trivial] using hy
  rw [he]
  apply isClosed_iInter
  intro v
  exact isClosed_le continuous_const
    (continuous_const.dotProduct ((continuous_lmi D).matrix_mulVec continuous_const))

theorem exists_optimal (c : Fin m → ℝ) (hsym : D.Symmetric)
    (hslater : D.Slater) (hcompact : D.InfCompact c) : ∃ y, D.IsOptimal c y := by
  obtain ⟨x0, t0, h0⟩ := hslater
  let y0 : (Fin m → ℝ) × ℝ := (x0, t0)
  let K : Set ((Fin m → ℝ) × ℝ) := {y | D.Feasible y ∧ c ⬝ᵥ y.1 ≤ c ⬝ᵥ y0.1}
  have hKclosed : IsClosed K := (isClosed_feasible D hsym).inter
    (isClosed_le (continuous_objective c) continuous_const)
  have hKcompact : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hKclosed, hcompact (c ⬝ᵥ y0.1)⟩
  have hKnonempty : K.Nonempty := ⟨y0, h0.posSemidef, le_rfl⟩
  obtain ⟨ystar, hystar, hmin⟩ := hKcompact.exists_isMinOn hKnonempty
    (continuous_objective c).continuousOn
  refine ⟨ystar, hystar.1, ?_⟩
  intro y hy
  by_cases hyle : c ⬝ᵥ y.1 ≤ c ⬝ᵥ y0.1
  · exact hmin ⟨hy, hyle⟩
  · exact hystar.2.trans (le_of_not_ge hyle)

end RobustSDP.Proof
end


/- Inlined checked module: MatrixTrace -/
section
open Matrix
open scoped MatrixOrder

namespace RobustSDP.Proof

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem exists_gram_factor {Z : Matrix ι ι ℝ} (hZ : Z.PosSemidef) :
    ∃ B : Matrix ι ι ℝ, Z = Bᵀ * B := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hZ.nonneg
  exact ⟨B, by simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hB⟩

theorem trace_mul_gram (A B : Matrix ι ι ℝ) :
    (A * (Bᵀ * B)).trace = (B * A * Bᵀ).trace := by
  classical
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]

theorem trace_mul_nonneg {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  obtain ⟨K, rfl⟩ := exists_gram_factor hB
  rw [trace_mul_gram]
  exact (hA.mul_mul_conjTranspose_same K).trace_nonneg

theorem trace_mul_eq_zero_iff_mul_eq_zero {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B).trace = 0 ↔ A * B = 0 := by
  classical
  constructor
  · intro h
    obtain ⟨P, rfl⟩ := exists_gram_factor hA
    obtain ⟨Q, rfl⟩ := exists_gram_factor hB
    rw [trace_mul_gram] at h
    have hzero : P * Qᵀ = 0 := by
      apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_assoc] using h
    calc
      (Pᵀ * P) * (Qᵀ * Q) = Pᵀ * (P * Qᵀ) * Q := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hzero]; simp
  · intro h
    simp [h]

theorem trace_weighted_gram_nonneg {Z : Matrix ι ι ℝ}
    (hZ : Z.PosSemidef) (R : Matrix κ ι ℝ) :
    0 ≤ (Z * (Rᵀ * R)).trace :=
  trace_mul_nonneg hZ (Matrix.posSemidef_conjTranspose_mul_self R)

theorem trace_mul_pos {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) (hB0 : B ≠ 0) : 0 < (A * B).trace := by
  classical
  apply lt_of_le_of_ne (trace_mul_nonneg hA.posSemidef hB)
  intro heq
  have hm := (trace_mul_eq_zero_iff_mul_eq_zero hA.posSemidef hB).mp heq.symm
  exact hB0 (hA.isUnit.mul_right_eq_zero.mp hm)

theorem trace_weighted_gram_eq_zero {Z : Matrix ι ι ℝ}
    (B : Matrix ι ι ℝ) (hB : Z = Bᵀ * B)
    (R : Matrix κ ι ℝ) :
    (Z * (Rᵀ * R)).trace = 0 ↔ R * Bᵀ = 0 := by
  classical
  subst Z
  have heq : ((Bᵀ * B) * (Rᵀ * R)).trace =
      ((R * Bᵀ)ᵀ * (R * Bᵀ)).trace := by
    calc
      ((Bᵀ * B) * (Rᵀ * R)).trace = ((Rᵀ * R) * (Bᵀ * B)).trace :=
        Matrix.trace_mul_comm _ _
      _ = (B * (Rᵀ * R) * Bᵀ).trace := trace_mul_gram _ _
      _ = ((R * Bᵀ)ᵀ * (R * Bᵀ)).trace := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [heq]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff

end RobustSDP.Proof
end


/- Inlined checked module: FeasibleSchur -/
section
open Matrix

namespace RobustSDP.Proof

theorem psd_entry_zero_of_diag_zero {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) (hi : A i i = 0) : A j i = 0 := by
  classical
  have hv : A *ᵥ Pi.single i 1 = 0 :=
    (hA.dotProduct_mulVec_zero_iff _).mp (by simpa using hi)
  simpa using congrFun hv j

variable {m n p q : ℕ} (D : RobustSDP.Uniqueness.SDPData m n p q)

theorem R_ne_zero_of_H3a (h3a : D.H3a) (x : Fin m → ℝ) : D.R x ≠ 0 := by
  obtain ⟨N, hN, hker⟩ := h3a
  intro hz
  have hk := hker 1 x (Or.inl one_ne_zero)
  have hp : D.pencil 1 x = 0 := by
    simpa only [RobustSDP.Uniqueness.SDPData.pencil, one_smul,
      RobustSDP.Uniqueness.SDPData.R] using hz
  rw [hp] at hk
  exact hN (by simpa using hk.symm)

theorem feasible_tau_pos (h3a : D.H3a) {y : (Fin m → ℝ) × ℝ}
    (hy : D.Feasible y) : 0 < y.2 := by
  classical
  have hR := R_ne_zero_of_H3a D h3a y.1
  obtain ⟨i, j, hij⟩ : ∃ i j, D.R y.1 i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hR (by ext i j; exact h i j)
  have hnonneg : 0 ≤ y.2 := by
    simpa [RobustSDP.Uniqueness.SDPData.lmi] using
      hy.diag_nonneg (i := Sum.inr i)
  apply lt_of_le_of_ne hnonneg
  intro ht
  have hd : D.lmi y.1 y.2 (Sum.inr i) (Sum.inr i) = 0 := by
    simp [RobustSDP.Uniqueness.SDPData.lmi, ← ht]
  have he := psd_entry_zero_of_diag_zero hy (Sum.inr i) (Sum.inl j) hd
  exact hij (by simpa [RobustSDP.Uniqueness.SDPData.lmi] using he)

noncomputable def schurFactor (R : Matrix (Fin q) (Fin n) ℝ) (t : ℝ) :
    Matrix (Fin n ⊕ Fin q) (Fin n) ℝ :=
  Matrix.fromRows 1 (-(t⁻¹ • R))

theorem schurFactor_identity (A : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin q) (Fin n) ℝ) {t : ℝ} (ht : t ≠ 0) :
    (schurFactor R t)ᵀ * Matrix.fromBlocks A Rᵀ R (t • 1) * schurFactor R t =
      A - t⁻¹ • (Rᵀ * R) := by
  simp only [schurFactor, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows,
    Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, Matrix.transpose_one,
    Matrix.transpose_neg, Matrix.transpose_smul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, inv_mul_cancel₀ ht, one_smul, add_neg_cancel, Matrix.mul_zero,
    add_zero, sub_eq_add_neg]

theorem feasible_G_posSemidef {y : (Fin m → ℝ) × ℝ}
    (hy : D.Feasible y) (ht : y.2 ≠ 0) : (D.G y).PosSemidef := by
  have h := hy.conjTranspose_mul_mul_same (schurFactor (D.R y.1) y.2)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial,
    RobustSDP.Uniqueness.SDPData.lmi, schurFactor_identity _ _ ht] at h
  exact h

end RobustSDP.Proof
end


/- Inlined checked module: BlockComplementarity -/
section
open Matrix

namespace RobustSDP.Proof

variable {n q : ℕ}

def topProjection : Matrix (Fin n) (Fin n ⊕ Fin q) ℝ := Matrix.fromCols 1 0

theorem kernel_factor {κ : Type*} (A : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin q) (Fin n) ℝ) {t : ℝ} (ht : t ≠ 0)
    (V : Matrix (Fin n ⊕ Fin q) κ ℝ)
    (hv : Matrix.fromBlocks A Rᵀ R (t • 1) * V = 0) :
    V = schurFactor R t * ((topProjection (n := n) (q := q)) * V) := by
  classical
  have hp : (topProjection (n := n) (q := q)) * V = V.submatrix Sum.inl id := by
    ext i j
    simp [topProjection, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type]
  rw [hp]
  ext (i | i) j
  · simp [schurFactor, Matrix.fromRows_mul]
  · have he := congrFun (congrFun hv (Sum.inr i)) j
    have he' : (R * V.submatrix Sum.inl id) i j + t * V (Sum.inr i) j = 0 := by
      simpa [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_sum_type] using he
    simp only [schurFactor, Matrix.fromRows_mul, Matrix.fromRows_apply_inr,
      Matrix.neg_mul, Matrix.smul_mul, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    nlinarith

theorem multiplier_block_factor (A : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin q) (Fin n) ℝ) {t : ℝ} (ht : t ≠ 0)
    {W : Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) ℝ}
    (hW : W.PosSemidef) (hA : (Matrix.fromBlocks A Rᵀ R (t • 1)).PosSemidef)
    (hcomp : (W * Matrix.fromBlocks A Rᵀ R (t • 1)).trace = 0) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
      W = schurFactor R t * Z * (schurFactor R t)ᵀ := by
  have hwzero : Matrix.fromBlocks A Rᵀ R (t • 1) * W = 0 := by
    apply (trace_mul_eq_zero_iff_mul_eq_zero hA hW).mp
    rwa [Matrix.trace_mul_comm]
  have hf := kernel_factor A R ht W hwzero
  have hs : Wᵀ = W := hW.isHermitian.eq
  have hft : W = W * (topProjection (n := n) (q := q))ᵀ * (schurFactor R t)ᵀ := by
    simpa only [Matrix.transpose_mul, hs] using congrArg Matrix.transpose hf
  refine ⟨(topProjection (n := n) (q := q)) * W * (topProjection (n := n) (q := q))ᵀ,
    hW.mul_mul_conjTranspose_same topProjection, ?_⟩
  calc
    W = schurFactor R t * ((topProjection (n := n) (q := q)) * W) := hf
    _ = schurFactor R t * ((topProjection (n := n) (q := q)) *
        (W * (topProjection (n := n) (q := q))ᵀ * (schurFactor R t)ᵀ)) := by rw [← hft]
    _ = schurFactor R t * ((topProjection (n := n) (q := q)) * W * (topProjection (n := n) (q := q))ᵀ) *
        (schurFactor R t)ᵀ := by simp only [Matrix.mul_assoc]

end RobustSDP.Proof
end


/- Inlined checked module: PerspectiveIdentity -/
section
open Matrix

namespace RobustSDP.Proof

variable {n q : ℕ}

theorem trace_sandwich {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix κ ι ℝ) (Z : Matrix ι ι ℝ) (A : Matrix κ κ ℝ) :
    ((H * Z * Hᵀ) * A).trace = (Z * (Hᵀ * A * H)).trace := by
  calc
    _ = (H * (Z * (Hᵀ * A))).trace := by simp only [Matrix.mul_assoc]
    _ = ((Z * (Hᵀ * A)) * H).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem schurFactor_sandwich (A : Matrix (Fin n) (Fin n) ℝ)
    (R S : Matrix (Fin q) (Fin n) ℝ) (t s : ℝ) :
    (schurFactor S s)ᵀ * Matrix.fromBlocks A Rᵀ R (t • 1) * schurFactor S s =
      A - s⁻¹ • (Rᵀ * S + Sᵀ * R) + (t * s⁻¹ ^ 2) • (Sᵀ * S) := by
  simp only [schurFactor, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows,
    Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows, Matrix.transpose_one,
    Matrix.transpose_neg, Matrix.transpose_smul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, smul_add, smul_neg, smul_smul,
    neg_neg]
  module

theorem perspective_matrix_identity (A : Matrix (Fin n) (Fin n) ℝ)
    (R S : Matrix (Fin q) (Fin n) ℝ) {t : ℝ} (ht : t ≠ 0) (s : ℝ) (hs : s ≠ 0) :
    (schurFactor S s)ᵀ * Matrix.fromBlocks A Rᵀ R (t • 1) * schurFactor S s =
      (A - t⁻¹ • (Rᵀ * R)) +
        t⁻¹ • ((R - (t / s) • S)ᵀ * (R - (t / s) • S)) := by
  rw [schurFactor_sandwich]
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add, smul_smul]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp [ht, hs]
  ring

theorem perspective_trace_identity (A : Matrix (Fin n) (Fin n) ℝ)
    (R S : Matrix (Fin q) (Fin n) ℝ) {t : ℝ} (ht : t ≠ 0) (s : ℝ) (hs : s ≠ 0)
    (Z : Matrix (Fin n) (Fin n) ℝ) :
    ((schurFactor S s * Z * (schurFactor S s)ᵀ) *
      Matrix.fromBlocks A Rᵀ R (t • 1)).trace =
      (Z * (A - t⁻¹ • (Rᵀ * R))).trace +
        t⁻¹ * (Z * ((R - (t / s) • S)ᵀ * (R - (t / s) • S))).trace := by
  calc
    _ = ((schurFactor S s) * (Z * ((schurFactor S s)ᵀ *
        Matrix.fromBlocks A Rᵀ R (t • 1)))).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((Z * ((schurFactor S s)ᵀ *
        Matrix.fromBlocks A Rᵀ R (t • 1))) * schurFactor S s).trace :=
      Matrix.trace_mul_comm _ _
    _ = (Z * ((schurFactor S s)ᵀ *
        Matrix.fromBlocks A Rᵀ R (t • 1) * schurFactor S s)).trace := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [perspective_matrix_identity A R S ht s hs, Matrix.mul_add, Matrix.trace_add,
        Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

end RobustSDP.Proof
end


/- Inlined checked module: PencilPositivity -/
section
open Matrix

namespace RobustSDP.Proof

variable {m n p q : ℕ} (D : RobustSDP.Uniqueness.SDPData m n p q)

theorem weighted_pencil_pos (h3a : D.H3a)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef)
    (xstar : Fin m → ℝ) (hstar : 0 < (Z * ((D.R xstar)ᵀ * D.R xstar)).trace)
    (lam : ℝ) (x : Fin m → ℝ) (hx : lam ≠ 0 ∨ x ≠ 0) :
    0 < (Z * ((D.pencil lam x)ᵀ * D.pencil lam x)).trace := by
  classical
  apply lt_of_le_of_ne (trace_weighted_gram_nonneg hZ _)
  intro hz
  obtain ⟨B, hB⟩ := exists_gram_factor hZ
  have hbzero := (trace_weighted_gram_eq_zero B hB (D.pencil lam x)).mp hz.symm
  obtain ⟨N, _, hker⟩ := h3a
  have hkR : LinearMap.ker (Matrix.toLin' (D.R xstar)) = N := by
    simpa only [RobustSDP.Uniqueness.SDPData.pencil, one_smul,
      RobustSDP.Uniqueness.SDPData.R] using hker 1 xstar (Or.inl one_ne_zero)
  have hrzero : D.R xstar * Bᵀ = 0 := by
    ext i j
    have hcol : (fun k => Bᵀ k j) ∈ LinearMap.ker (Matrix.toLin' (D.pencil lam x)) := by
      change (D.pencil lam x) *ᵥ (fun k => Bᵀ k j) = 0
      funext k
      exact congrFun (congrFun hbzero k) j
    rw [hker lam x hx, ← hkR] at hcol
    change (D.R xstar) *ᵥ (fun k => Bᵀ k j) = 0 at hcol
    exact congrFun hcol i
  have htrace := (trace_weighted_gram_eq_zero B hB (D.R xstar)).mpr hrzero
  exact hstar.ne' htrace

theorem weighted_R_pos_of_stationarity (h3b : D.H3b)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef) (hZ0 : Z ≠ 0)
    (xstar : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0)
    (hstation : (Z * ((D.R xstar)ᵀ * D.R xstar)).trace =
      s ^ 2 * (Z * (D.L * D.Lᵀ)).trace) :
    0 < (Z * ((D.R xstar)ᵀ * D.R xstar)).trace := by
  classical
  apply lt_of_le_of_ne (trace_weighted_gram_nonneg hZ _)
  intro hz
  have hL : (Z * (D.L * D.Lᵀ)).trace = 0 := by
    have hs2 : s ^ 2 ≠ 0 := pow_ne_zero _ hs
    exact (mul_eq_zero.mp (hstation.symm.trans hz.symm)).resolve_left hs2
  obtain ⟨B, hB⟩ := exists_gram_factor hZ
  have hRzero := (trace_weighted_gram_eq_zero B hB (D.R xstar)).mp hz.symm
  have hLzero : D.Lᵀ * Bᵀ = 0 :=
    (trace_weighted_gram_eq_zero B hB D.Lᵀ).mp (by simpa using hL)
  have hBzero : Bᵀ = 0 := by
    ext i j
    have hv : Matrix.fromRows D.Lᵀ (D.R xstar) *ᵥ (fun k => Bᵀ k j) = 0 := by
      funext k
      cases k with
      | inl k => exact congrFun (congrFun hLzero k) j
      | inr k => exact congrFun (congrFun hRzero k) j
    have he : (fun k => Bᵀ k j) = 0 :=
      h3b xstar (hv.trans (Matrix.mulVec_zero _).symm)
    exact congrFun he i
  exact hZ0 (by rw [hB, hBzero, Matrix.zero_mul])

end RobustSDP.Proof
end


/- Inlined checked module: QuadraticCoercivity -/
section
namespace RobustSDP.Proof

theorem continuous_quadratic_lower {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] (u : E) (hu : ‖u‖ = 1)
    (Q : E → ℝ) (hcont : Continuous Q) (hpos : ∀ v, v ≠ 0 → 0 < Q v)
    (hscale : ∀ (r : ℝ) v, Q (r • v) = r ^ 2 * Q v) :
    ∃ k : ℝ, 0 < k ∧ ∀ v, k * ‖v‖ ^ 2 ≤ Q v := by
  have hne : (Metric.sphere (0 : E) 1).Nonempty :=
    ⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩
  obtain ⟨z, hz, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hcont.continuousOn
  have hz1 : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz1
  refine ⟨Q z, hpos z hz0, fun v => ?_⟩
  by_cases hv : v = 0
  · subst v
    have hzero : Q 0 = 0 := by simpa using hscale 0 0
    simp [hzero]
  · have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hunit : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      exact norm_smul_inv_norm hv
    have hm : Q z ≤ ‖v‖⁻¹ ^ 2 * Q v := by
      have hm0 : Q z ≤ Q (‖v‖⁻¹ • v) := hmin hunit
      rw [hscale] at hm0
      exact hm0
    calc
      Q z * ‖v‖ ^ 2 = ‖v‖ ^ 2 * Q z := mul_comm _ _
      _ ≤ ‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * Q v) :=
        mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _ = Q v := by field_simp

theorem sqDist_zero_le_norm {m : ℕ} (v : (Fin m → ℝ) × ℝ) :
    RobustSDP.Uniqueness.SDPData.sqDist v 0 ≤ ((m : ℝ) + 1) * ‖v‖ ^ 2 := by
  have hfirst (i : Fin m) : (v.1 i) ^ 2 ≤ ‖v‖ ^ 2 := by
    have h := (norm_le_pi_norm v.1 i).trans (norm_fst_le v)
    simpa only [Real.norm_eq_abs, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg (v.1 i)) h 2
  have hsecond : v.2 ^ 2 ≤ ‖v‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg v.2) (norm_snd_le v) 2
  have hsum := Finset.sum_le_sum (fun (i : Fin m) (_ : i ∈ Finset.univ) => hfirst i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  simp only [RobustSDP.Uniqueness.SDPData.sqDist, Prod.fst_zero, Prod.snd_zero,
    Pi.zero_apply, sub_zero]
  nlinarith

theorem continuous_quadratic_sqDist_lower {m : ℕ}
    (Q : ((Fin m → ℝ) × ℝ) → ℝ) (hcont : Continuous Q)
    (hpos : ∀ v, v ≠ 0 → 0 < Q v)
    (hscale : ∀ (r : ℝ) v, Q (r • v) = r ^ 2 * Q v) :
    ∃ k : ℝ, 0 < k ∧ ∀ v,
      k * RobustSDP.Uniqueness.SDPData.sqDist v 0 ≤ Q v := by
  obtain ⟨k, hk, hbound⟩ := continuous_quadratic_lower
    (E := (Fin m → ℝ) × ℝ) (0, 1) (by simp) Q hcont hpos hscale
  have hm : 0 < (m : ℝ) + 1 := by positivity
  refine ⟨k / ((m : ℝ) + 1), div_pos hk hm, fun v => ?_⟩
  calc
    _ ≤ (k / ((m : ℝ) + 1)) * (((m : ℝ) + 1) * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (sqDist_zero_le_norm v) (div_nonneg hk.le hm.le)
    _ = k * ‖v‖ ^ 2 := by field_simp
    _ ≤ Q v := hbound v

end RobustSDP.Proof
end


/- Inlined checked module: PencilCoercivity -/
section
open Matrix

namespace RobustSDP.Proof

variable {m n p q : ℕ} (D : RobustSDP.Uniqueness.SDPData m n p q)

noncomputable def shiftedPencil (xstar : Fin m → ℝ) (s : ℝ)
    (v : (Fin m → ℝ) × ℝ) : Matrix (Fin q) (Fin n) ℝ :=
  (∑ i, v.1 i • D.Rs i) - (v.2 / s) • D.R xstar

theorem shiftedPencil_eq_pencil (xstar : Fin m → ℝ) (s : ℝ)
    (v : (Fin m → ℝ) × ℝ) :
    shiftedPencil D xstar s v =
      D.pencil (-(v.2 / s)) (fun i => v.1 i - (v.2 / s) * xstar i) := by
  simp only [shiftedPencil, RobustSDP.Uniqueness.SDPData.pencil,
    RobustSDP.Uniqueness.SDPData.R, sub_smul, smul_add, Finset.smul_sum,
    Finset.sum_sub_distrib, mul_smul, neg_smul]
  abel

theorem shiftedPencil_smul (xstar : Fin m → ℝ) (s r : ℝ)
    (v : (Fin m → ℝ) × ℝ) :
    shiftedPencil D xstar s (r • v) = r • shiftedPencil D xstar s v := by
  simp only [shiftedPencil, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    mul_div_assoc, smul_sub, Finset.smul_sum, smul_smul]

theorem shiftedPencil_continuous (xstar : Fin m → ℝ) (s : ℝ) :
    Continuous (shiftedPencil D xstar s) := by
  unfold shiftedPencil
  fun_prop

theorem shiftedPencil_displacement (xstar x : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0)
    (t : ℝ) :
    shiftedPencil D xstar s ((x, t) - (xstar, s)) = D.R x - (t / s) • D.R xstar := by
  have hcoef : (t - s) / s = t / s - 1 := by field_simp
  change (∑ i, (x i - xstar i) • D.Rs i) - ((t - s) / s) • D.R xstar = _
  simp only [sub_smul, Finset.sum_sub_distrib, hcoef, one_smul,
    RobustSDP.Uniqueness.SDPData.R, smul_add]
  module

theorem shiftedPencil_weighted_pos (h3a : D.H3a)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef)
    (xstar : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0)
    (hstar : 0 < (Z * ((D.R xstar)ᵀ * D.R xstar)).trace)
    (v : (Fin m → ℝ) × ℝ) (hv : v ≠ 0) :
    0 < (Z * ((shiftedPencil D xstar s v)ᵀ * shiftedPencil D xstar s v)).trace := by
  rw [shiftedPencil_eq_pencil]
  apply weighted_pencil_pos D h3a hZ xstar hstar
  by_cases ht : v.2 = 0
  · right
    simpa only [ht, zero_div, zero_mul, sub_zero] using
      (show v.1 ≠ 0 from fun hx => hv (Prod.ext hx ht))
  · exact Or.inl (neg_ne_zero.mpr (div_ne_zero ht hs))

theorem shiftedPencil_coercive (h3a : D.H3a)
    {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef)
    (xstar : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0)
    (hstar : 0 < (Z * ((D.R xstar)ᵀ * D.R xstar)).trace) :
    ∃ k : ℝ, 0 < k ∧ ∀ v : (Fin m → ℝ) × ℝ,
      k * RobustSDP.Uniqueness.SDPData.sqDist v 0 ≤
        (Z * ((shiftedPencil D xstar s v)ᵀ * shiftedPencil D xstar s v)).trace := by
  apply continuous_quadratic_sqDist_lower
  · have hc := shiftedPencil_continuous D xstar s
    fun_prop
  · exact shiftedPencil_weighted_pos D h3a hZ xstar hs hstar
  · intro r v
    rw [shiftedPencil_smul]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.trace_smul, smul_eq_mul, pow_two]

end RobustSDP.Proof
end


/- Inlined checked module: GrowthConsequences -/
section
open Matrix
open RobustSDP.Uniqueness

namespace RobustSDP.Proof

variable {m n p q : ℕ}

theorem sqDist_nonneg (y z : (Fin m → ℝ) × ℝ) : 0 ≤ SDPData.sqDist y z :=
  add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)

theorem sqDist_eq_zero_iff (y z : (Fin m → ℝ) × ℝ) :
    SDPData.sqDist y z = 0 ↔ y = z := by
  constructor
  · intro h
    have hsum : ∑ i, (y.1 i - z.1 i) ^ 2 = 0 := by
      have := sq_nonneg (y.2 - z.2)
      have := Finset.sum_nonneg (fun (i : Fin m) (_ : i ∈ Finset.univ) =>
        sq_nonneg (y.1 i - z.1 i))
      unfold SDPData.sqDist at h
      linarith
    have hcoord := (Finset.sum_eq_zero_iff_of_nonneg
      (fun (i : Fin m) (_ : i ∈ Finset.univ) => sq_nonneg (y.1 i - z.1 i))).mp hsum
    apply Prod.ext
    · funext i
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hcoord i (Finset.mem_univ i)))
    · unfold SDPData.sqDist at h
      rw [hsum, zero_add] at h
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp h)
  · rintro rfl
    simp [SDPData.sqDist]

theorem qgc_of_weighted_growth (D : SDPData m n p q) (c : Fin m → ℝ)
    (ystar : (Fin m → ℝ) × ℝ) (hopt : D.IsOptimal c ystar)
    (hs : 0 < ystar.2) (k : ℝ) (hk : 0 < k)
    (hgrowth : ∀ y, D.Feasible y →
      k * SDPData.sqDist y ystar ≤ y.2 * (c ⬝ᵥ y.1 - c ⬝ᵥ ystar.1)) :
    D.QGC c ystar := by
  refine ⟨k / (2 * ystar.2), div_pos hk (mul_pos (by norm_num) hs),
    ystar.2, hs, fun y hy hnear => ?_⟩
  have hsum : 0 ≤ ∑ i, (y.1 i - ystar.1 i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have htime : y.2 < 2 * ystar.2 := by
    unfold SDPData.sqDist at hnear
    by_contra hnot
    have ht : 2 * ystar.2 ≤ y.2 := le_of_not_gt hnot
    have hprod : 0 ≤ y.2 * (y.2 - 2 * ystar.2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hgap : 0 ≤ c ⬝ᵥ y.1 - c ⬝ᵥ ystar.1 := sub_nonneg.mpr (hopt.2 y hy)
  have hbound := (hgrowth y hy).trans (mul_le_mul_of_nonneg_right htime.le hgap)
  have hdiv : (k * SDPData.sqDist y ystar) / (2 * ystar.2) ≤
      c ⬝ᵥ y.1 - c ⬝ᵥ ystar.1 :=
    (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hs)).mpr
      (by simpa only [mul_comm] using hbound)
  have halpha : k / (2 * ystar.2) * SDPData.sqDist y ystar ≤
      c ⬝ᵥ y.1 - c ⬝ᵥ ystar.1 := by
    convert hdiv using 1
    ring
  linarith

theorem optimal_unique_of_weighted_growth (D : SDPData m n p q) (c : Fin m → ℝ)
    (ystar : (Fin m → ℝ) × ℝ) (hopt : D.IsOptimal c ystar)
    (k : ℝ) (hk : 0 < k)
    (hgrowth : ∀ y, D.Feasible y →
      k * SDPData.sqDist y ystar ≤ y.2 * (c ⬝ᵥ y.1 - c ⬝ᵥ ystar.1)) :
    ∀ y, D.IsOptimal c y → y = ystar := by
  intro y hy
  have he : c ⬝ᵥ y.1 = c ⬝ᵥ ystar.1 := le_antisymm
    (hy.2 ystar hopt.1) (hopt.2 y hy.1)
  have hb := hgrowth y hy.1
  rw [he, sub_self, mul_zero] at hb
  have hd := sqDist_nonneg y ystar
  exact (sqDist_eq_zero_iff y ystar).mp (by nlinarith)

end RobustSDP.Proof
end


/- Inlined checked module: MultiplierCertificate -/
section
open Matrix

namespace RobustSDP.Proof

variable {m n p q : ℕ}

structure MultiplierCertificate (D : RobustSDP.Uniqueness.SDPData m n p q)
    (c : Fin m → ℝ) (ystar : (Fin m → ℝ) × ℝ) where
  matrix : Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) ℝ
  posSemidef : matrix.PosSemidef
  value : ∀ y : (Fin m → ℝ) × ℝ,
    (matrix * D.lmi y.1 y.2).trace = c ⬝ᵥ y.1 - c ⬝ᵥ ystar.1

namespace MultiplierCertificate

variable {D : RobustSDP.Uniqueness.SDPData m n p q} {c : Fin m → ℝ}
  {ystar : (Fin m → ℝ) × ℝ} (C : MultiplierCertificate D c ystar)

theorem complementarity : (C.matrix * D.lmi ystar.1 ystar.2).trace = 0 := by
  simpa using C.value ystar

theorem matrix_ne_zero (hc : c ≠ 0) : C.matrix ≠ 0 := by
  classical
  intro hz
  apply hc
  funext i
  have h := C.value (ystar.1 + Pi.single i 1, ystar.2)
  simpa [hz, dotProduct_add] using h.symm

theorem tau_stationarity :
    (C.matrix * Matrix.fromBlocks (-(D.L * D.Lᵀ))
      (0 : Matrix (Fin n) (Fin q) ℝ) (0 : Matrix (Fin q) (Fin n) ℝ)
      (1 : Matrix (Fin q) (Fin q) ℝ)).trace = 0 := by
  have he : D.lmi ystar.1 (ystar.2 + 1) - D.lmi ystar.1 ystar.2 =
      Matrix.fromBlocks (-(D.L * D.Lᵀ))
      (0 : Matrix (Fin n) (Fin q) ℝ) (0 : Matrix (Fin q) (Fin n) ℝ)
      (1 : Matrix (Fin q) (Fin q) ℝ) := by
    ext (i | i) (j | j) <;>
      simp [RobustSDP.Uniqueness.SDPData.lmi, add_smul, sub_eq_add_neg]
    ring
  rw [← he, Matrix.mul_sub, Matrix.trace_sub, C.value (ystar.1, ystar.2 + 1), C.value ystar]
  simp

theorem factor {hs : ystar.2 ≠ 0} (hfeas : D.Feasible ystar) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
      C.matrix = schurFactor (D.R ystar.1) ystar.2 * Z *
        (schurFactor (D.R ystar.1) ystar.2)ᵀ :=
  multiplier_block_factor (D.F ystar.1 - ystar.2 • (D.L * D.Lᵀ))
    (D.R ystar.1) hs C.posSemidef hfeas C.complementarity

theorem factor_tau_stationarity {Z : Matrix (Fin n) (Fin n) ℝ}
    (hs : ystar.2 ≠ 0)
    (hfactor : C.matrix = schurFactor (D.R ystar.1) ystar.2 * Z *
      (schurFactor (D.R ystar.1) ystar.2)ᵀ) :
    (Z * ((D.R ystar.1)ᵀ * D.R ystar.1)).trace =
      ystar.2 ^ 2 * (Z * (D.L * D.Lᵀ)).trace := by
  have h := C.tau_stationarity
  rw [hfactor, trace_sandwich] at h
  have hsand : (schurFactor (D.R ystar.1) ystar.2)ᵀ *
      Matrix.fromBlocks (-(D.L * D.Lᵀ))
      (0 : Matrix (Fin n) (Fin q) ℝ) (0 : Matrix (Fin q) (Fin n) ℝ)
      (1 : Matrix (Fin q) (Fin q) ℝ) *
        schurFactor (D.R ystar.1) ystar.2 =
      -(D.L * D.Lᵀ) + (ystar.2⁻¹ ^ 2) • ((D.R ystar.1)ᵀ * D.R ystar.1) := by
    simpa only [Matrix.transpose_zero, one_smul, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, smul_zero, sub_zero, one_mul] using
      schurFactor_sandwich (-(D.L * D.Lᵀ)) 0 (D.R ystar.1) 1 ystar.2
  rw [hsand, Matrix.mul_add, Matrix.trace_add, Matrix.mul_neg, Matrix.trace_neg,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at h
  field_simp [hs] at h
  nlinarith

theorem positive_factor (hc : c ≠ 0) (h3a : D.H3a) (h3b : D.H3b)
    (hfeas : D.Feasible ystar) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Z.PosSemidef ∧
      C.matrix = schurFactor (D.R ystar.1) ystar.2 * Z *
        (schurFactor (D.R ystar.1) ystar.2)ᵀ ∧
      0 < (Z * ((D.R ystar.1)ᵀ * D.R ystar.1)).trace := by
  have hs := feasible_tau_pos D h3a hfeas
  obtain ⟨Z, hZ, hfactor⟩ := C.factor (hs := hs.ne') hfeas
  have hZ0 : Z ≠ 0 := by
    intro hz
    exact C.matrix_ne_zero hc (by simp [hz] at hfactor; exact hfactor)
  exact ⟨Z, hZ, hfactor, weighted_R_pos_of_stationarity D h3b hZ hZ0 ystar.1 hs.ne'
    (C.factor_tau_stationarity hs.ne' hfactor)⟩

end MultiplierCertificate

end RobustSDP.Proof
end


/- Inlined checked module: CertificateGrowth -/
section
open Matrix
open RobustSDP.Uniqueness

namespace RobustSDP.Proof

variable {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ)
  (ystar : (Fin m → ℝ) × ℝ)

theorem certificate_weighted_growth (hc : c ≠ 0) (h3a : D.H3a) (h3b : D.H3b)
    (hfeas : D.Feasible ystar) (C : MultiplierCertificate D c ystar) :
    ∃ k : ℝ, 0 < k ∧ ∀ y, D.Feasible y →
      k * SDPData.sqDist y ystar ≤ y.2 * (c ⬝ᵥ y.1 - c ⬝ᵥ ystar.1) := by
  have hs := feasible_tau_pos D h3a hfeas
  obtain ⟨Z, hZ, hfactor, hRpos⟩ := C.positive_factor hc h3a h3b hfeas
  obtain ⟨k, hk, hbound⟩ := shiftedPencil_coercive D h3a hZ ystar.1 hs.ne' hRpos
  refine ⟨k, hk, fun y hy => ?_⟩
  have ht := feasible_tau_pos D h3a hy
  have hG := feasible_G_posSemidef D hy ht.ne'
  have hGtrace := trace_mul_nonneg hZ hG
  have hpers := perspective_trace_identity (D.F y.1 - y.2 • (D.L * D.Lᵀ))
    (D.R y.1) (D.R ystar.1) ht.ne' ystar.2 hs.ne' Z
  rw [← hfactor, ← SDPData.lmi, C.value] at hpers
  change c ⬝ᵥ y.1 - c ⬝ᵥ ystar.1 = (Z * D.G y).trace +
    y.2⁻¹ * (Z * ((D.R y.1 - (y.2 / ystar.2) • D.R ystar.1)ᵀ *
      (D.R y.1 - (y.2 / ystar.2) • D.R ystar.1))).trace at hpers
  have hB := hbound (y - ystar)
  rw [shiftedPencil_displacement D ystar.1 y.1 hs.ne' y.2] at hB
  have hd : SDPData.sqDist (y - ystar) 0 = SDPData.sqDist y ystar := by
    simp [SDPData.sqDist]
  rw [hd] at hB
  have heq : y.2 * (c ⬝ᵥ y.1 - c ⬝ᵥ ystar.1) =
      y.2 * (Z * D.G y).trace +
        (Z * ((D.R y.1 - (y.2 / ystar.2) • D.R ystar.1)ᵀ *
          (D.R y.1 - (y.2 / ystar.2) • D.R ystar.1))).trace := by
    rw [hpers]
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  rw [heq]
  exact hB.trans (le_add_of_nonneg_left (mul_nonneg ht.le hGtrace))

theorem qgc_of_certificate (hc : c ≠ 0) (h3a : D.H3a) (h3b : D.H3b)
    (hopt : D.IsOptimal c ystar) (C : MultiplierCertificate D c ystar) :
    D.QGC c ystar := by
  obtain ⟨k, hk, hg⟩ := certificate_weighted_growth D c ystar hc h3a h3b hopt.1 C
  exact qgc_of_weighted_growth D c ystar hopt (feasible_tau_pos D h3a hopt.1) k hk hg

theorem uniqueness_of_certificate (hc : c ≠ 0) (h3a : D.H3a) (h3b : D.H3b)
    (hopt : D.IsOptimal c ystar) (C : MultiplierCertificate D c ystar) :
    ∀ y, D.IsOptimal c y → y = ystar := by
  obtain ⟨k, hk, hg⟩ := certificate_weighted_growth D c ystar hc h3a h3b hopt.1 C
  exact optimal_unique_of_weighted_growth D c ystar hopt k hk hg

end RobustSDP.Proof
end


/- Inlined checked module: CanonicalMultiplier -/
section
open Matrix

noncomputable section

namespace RobustSDP.Proof

variable {m n p q : ℕ} (D : RobustSDP.Uniqueness.SDPData m n p q)

def lmiLinear : ((Fin m → ℝ) × ℝ) →ₗ[ℝ]
    Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) ℝ where
  toFun y := D.lmi y.1 y.2 - D.lmi 0 0
  map_add' y z := by
    ext (i | i) (j | j)
    all_goals
      simp [RobustSDP.Uniqueness.SDPData.lmi, RobustSDP.Uniqueness.SDPData.F,
        RobustSDP.Uniqueness.SDPData.R, add_smul, Finset.sum_add_distrib]
      <;> ring
  map_smul' a y := by
    ext (i | i) (j | j)
    all_goals
      simp [RobustSDP.Uniqueness.SDPData.lmi, RobustSDP.Uniqueness.SDPData.F,
        RobustSDP.Uniqueness.SDPData.R, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, Finset.mul_sum, mul_assoc]
    all_goals
      rw [← Finset.mul_sum]
      ring

def objectiveLinear (c : Fin m → ℝ) : ((Fin m → ℝ) × ℝ) →ₗ[ℝ] ℝ where
  toFun y := c ⬝ᵥ y.1
  map_add' _ _ := dotProduct_add _ _ _
  map_smul' a y := by
    change c ⬝ᵥ (a • y.1) = a * (c ⬝ᵥ y.1)
    simp only [dotProduct_smul, smul_eq_mul]

theorem exists_multiplierCertificate (c : Fin m → ℝ) (hsym : D.Symmetric)
    (hslater : D.Slater) (ystar : (Fin m → ℝ) × ℝ) (hopt : D.IsOptimal c ystar) :
    Nonempty (MultiplierCertificate D c ystar) := by
  let A0 : SymMat (Fin n ⊕ Fin q) := symmetrize (D.lmi 0 0)
  let A : ((Fin m → ℝ) × ℝ) →ₗ[ℝ] SymMat (Fin n ⊕ Fin q) :=
    symmetrize.comp (lmiLinear D)
  have he (y : (Fin m → ℝ) × ℝ) :
      ((A0 + A y : SymMat (Fin n ⊕ Fin q)) : Matrix _ _ ℝ) = D.lmi y.1 y.2 := by
    have hsum : A0 + A y = symmetrize (D.lmi y.1 y.2) := by
      change symmetrize (D.lmi 0 0) + symmetrize (D.lmi y.1 y.2 - D.lmi 0 0) = _
      rw [map_sub]
      abel
    rw [hsum]
    exact congrArg Subtype.val (symmetrize_coe
      (symMatOf (D.lmi y.1 y.2) (lmi_isHermitian D hsym _ _)))
  obtain ⟨W, hW, hv⟩ := affine_slater_multiplier A0 A (objectiveLinear c) ystar
    (by rw [he]; exact hopt.1)
    (by intro y hy; rw [he] at hy; exact hopt.2 y hy)
    (by obtain ⟨x, t, ht⟩ := hslater; exact ⟨(x, t), by simpa only [he] using ht⟩)
  refine ⟨⟨W, hW, ?_⟩⟩
  intro y
  have h := hv y
  change (W * (A0 + A y : SymMat (Fin n ⊕ Fin q))).trace =
    c ⬝ᵥ y.1 - c ⬝ᵥ ystar.1 at h
  rw [he] at h
  exact h

end RobustSDP.Proof
end
end


/- Inlined checked module: RobustRoot -/
section
open Matrix

namespace RobustSDP.Uniqueness

/-- **Theorem 4.2** (El Ghaoui–Oustry–Lebret 1998, p. 39). If H1–H3 hold, the SDP (15) satisfies the
quadratic growth condition at every optimal point `y_opt = (x_opt, τ_opt)`; consequently (15) has
a unique solution `(x, τ)`. Standing assumptions: `c ≠ 0` and `F₀, …, F_m` symmetric (p. 33). -/
theorem theorem_4_2 {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (hc : c ≠ 0)
    (hsym : D.Symmetric) (h1 : D.Slater) (h2 : D.InfCompact c) (h3a : D.H3a) (h3b : D.H3b) :
    (∀ y : (Fin m → ℝ) × ℝ, D.IsOptimal c y → D.QGC c y) ∧
      ∃! y : (Fin m → ℝ) × ℝ, D.IsOptimal c y := by
  constructor
  · intro y hy
    obtain ⟨C⟩ := Proof.exists_multiplierCertificate D c hsym h1 y hy
    exact Proof.qgc_of_certificate D c y hc h3a h3b hy C
  · obtain ⟨ystar, hstar⟩ := Proof.exists_optimal D c hsym h1 h2
    obtain ⟨C⟩ := Proof.exists_multiplierCertificate D c hsym h1 ystar hstar
    exact ⟨ystar, hstar, Proof.uniqueness_of_certificate D c ystar hc h3a h3b hstar C⟩

end RobustSDP.Uniqueness

open RobustSDP.Uniqueness

theorem solution {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (hc : c ≠ 0)
    (hsym : D.Symmetric) (h1 : D.Slater) (h2 : D.InfCompact c) (h3a : D.H3a) (h3b : D.H3b) :
    (∀ y : (Fin m → ℝ) × ℝ, D.IsOptimal c y → D.QGC c y) ∧
      ∃! y : (Fin m → ℝ) × ℝ, D.IsOptimal c y := RobustSDP.Uniqueness.theorem_4_2 D c hc hsym h1 h2 h3a h3b
end
