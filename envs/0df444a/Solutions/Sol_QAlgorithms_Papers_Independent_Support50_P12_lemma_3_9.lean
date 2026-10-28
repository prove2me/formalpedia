-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.lemma_3_9
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:43:28.78543+00:00
-- url     : https://prove2.me/submissions/f74dc318-6170-4db4-9cea-75b1a0045f20

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]


section S169H
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma S169H_herm_of_hermitian (A : Alg I) (Phi : MatrixMap I J)
    (hpos : PositiveOnConcreteAlgebra A Phi) (H : Mat I) (hA : H ∈ A) (hH : H.IsHermitian) :
    (Phi H).IsHermitian := by
  set r : ℝ := ‖H‖
  have h0 : 0 ≤ H + algebraMap ℝ (Mat I) r := by
    have := IsSelfAdjoint.neg_algebraMap_norm_le_self (a := H) hH
    rw [← sub_nonneg] at this; simpa [sub_neg_eq_add] using this
  have halg : algebraMap ℝ (Mat I) r = ((r : ℂ)) • (1 : Mat I) := by
    rw [Algebra.algebraMap_eq_smul_one]; rw [← Complex.coe_smul]
  rw [halg] at h0
  have hmem : H + ((r : ℂ)) • (1 : Mat I) ∈ A := A.add_mem hA (A.smul_mem A.one_mem _)
  have hP1 := hpos _ hmem (Matrix.nonneg_iff_posSemidef.mp h0)
  have hP2 := hpos _ A.one_mem Matrix.PosSemidef.one
  have e : Phi H = Phi (H + ((r : ℂ)) • (1 : Mat I)) - ((r : ℂ)) • Phi 1 := by
    rw [map_add, map_smul]; abel
  rw [e]
  refine hP1.1.sub ?_
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hP2.1.eq, Complex.star_def, Complex.conj_ofReal]

lemma S169H_herm (A : Alg I) (Phi : MatrixMap I J)
    (hpos : PositiveOnConcreteAlgebra A Phi) (X : Mat I) (hX : X ∈ A) :
    Phi Xᴴ = (Phi X)ᴴ := by
  set H1 : Mat I := (1/2 : ℂ) • (X + Xᴴ)
  set H2 : Mat I := (-Complex.I/2) • (X - Xᴴ)
  have hXs : Xᴴ ∈ A := by rw [← Matrix.star_eq_conjTranspose]; exact star_mem hX
  have h1A : H1 ∈ A := A.smul_mem (A.add_mem hX hXs) _
  have h2A : H2 ∈ A := A.smul_mem (A.sub_mem hX hXs) _
  have h1H : H1.IsHermitian := by
    unfold Matrix.IsHermitian
    simp only [H1, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    rw [add_comm]; congr 1; simp [Complex.star_def]
  have h2H : H2.IsHermitian := by
    unfold Matrix.IsHermitian
    simp only [H2, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    rw [show (Xᴴ - X) = -(X - Xᴴ) by abel, smul_neg, ← neg_smul]
    congr 1; simp [Complex.star_def, Complex.conj_I]; ring
  have eX : X = H1 + Complex.I • H2 := by
    simp only [H1, H2, smul_sub, smul_add, smul_smul]
    ext i j; simp; ring_nf; rw [Complex.I_sq]; ring
  have eXs : Xᴴ = H1 - Complex.I • H2 := by
    simp only [H1, H2, smul_sub, smul_add, smul_smul]
    ext i j; simp; ring_nf; rw [Complex.I_sq]; ring
  have p1 := S169H_herm_of_hermitian A Phi hpos H1 h1A h1H
  have p2 := S169H_herm_of_hermitian A Phi hpos H2 h2A h2H
  clear_value H1 H2
  rw [eXs, eX, map_sub, map_add, map_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, p1.eq, p2.eq, Complex.star_def, Complex.conj_I, neg_smul, sub_eq_add_neg]

end S169H

lemma S169H_valid (A : Alg I) (Phi : MatrixMap I J) (hp : AlgebraSchwarzMap A Phi) :
    SchwarzBound A Phi (snorm A Phi).toReal := by
  obtain ⟨r0, hr0⟩ := hp
  have hpos := hr0.2.1
  have hfin : snorm A Phi ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (sInf_le ⟨r0, hr0, rfl⟩)
  refine ⟨ENNReal.toReal_nonneg, hpos, fun X hX => ?_⟩
  have hXs : Xᴴ ∈ A := by rw [← Matrix.star_eq_conjTranspose]; exact star_mem hX
  have hP : (Phi (Xᴴ * X)).PosSemidef :=
    hpos _ (A.mul_mem hXs hX) (Matrix.posSemidef_conjTranspose_mul_self X)
  have hQ : ((Phi X)ᴴ * Phi X).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  set c := (snorm A Phi).toReal
  show (((c : ℂ)) • Phi (Xᴴ * X) - (Phi X)ᴴ * Phi X).PosSemidef
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hP.1.eq, hQ.1.eq, Complex.star_def,
      Complex.conj_ofReal]
  · intro v
    have expand : ∀ r : ℝ, star v ⬝ᵥ ((((r : ℂ)) • Phi (Xᴴ * X) - (Phi X)ᴴ * Phi X) *ᵥ v) =
        (r : ℂ) * (star v ⬝ᵥ (Phi (Xᴴ * X) *ᵥ v)) - star v ⬝ᵥ (((Phi X)ᴴ * Phi X) *ᵥ v) := by
      intro r
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have hv : ∀ r, SchwarzBound A Phi r →
        0 ≤ star v ⬝ᵥ ((((r : ℂ)) • Phi (Xᴴ * X) - (Phi X)ᴴ * Phi X) *ᵥ v) :=
      fun r hr => (hr.2.2 X hX).dotProduct_mulVec_nonneg v
    set p := star v ⬝ᵥ (Phi (Xᴴ * X) *ᵥ v)
    set q := star v ⬝ᵥ (((Phi X)ᴴ * Phi X) *ᵥ v)
    have hp0 := Complex.nonneg_iff.mp (hP.dotProduct_mulVec_nonneg v)
    have hq0 := Complex.nonneg_iff.mp (hQ.dotProduct_mulVec_nonneg v)
    have hvr : ∀ r, SchwarzBound A Phi r → q.re ≤ r * p.re := by
      intro r hr
      have := Complex.nonneg_iff.mp (hv r hr)
      rw [expand] at this
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero] at this
      linarith [this.1]
    rw [expand, Complex.nonneg_iff]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.sub_im, Complex.mul_im, zero_add]
    refine ⟨?_, by rw [← hp0.2, ← hq0.2]; ring⟩
    rcases eq_or_lt_of_le hp0.1 with h0 | h0
    · have := hvr r0 hr0; rw [← h0] at this ⊢; linarith
    · have hle : ENNReal.ofReal (q.re / p.re) ≤ snorm A Phi := by
        apply le_sInf
        rintro b ⟨r, hr, rfl⟩
        exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ h0).mpr (by linarith [hvr r hr]))
      have := (ENNReal.ofReal_le_iff_le_toReal hfin).mp hle
      rw [div_le_iff₀ h0] at this
      linarith

lemma S169H_quad_zero {J : Type} [Fintype J] [DecidableEq J] (N : Mat J)
    (h : ∀ v : J → ℂ, star v ⬝ᵥ (N *ᵥ v) = 0) : N = 0 := by
  have hT : Matrix.toEuclideanLin N = 0 := by
    rw [← inner_map_self_eq_zero]
    intro x
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have := h (WithLp.ofLp x)
    have e : (WithLp.ofLp x) ⬝ᵥ star (WithLp.ofLp (Matrix.toEuclideanLin N x)) =
        star (star (WithLp.ofLp x) ⬝ᵥ (N *ᵥ WithLp.ofLp x)) := by
      rw [Matrix.toEuclideanLin_apply]
      simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
    rw [e, this, star_zero]
  exact (Matrix.toEuclideanLin).injective (by rw [hT, map_zero])

lemma S169H_dot_adj {J : Type} [Fintype J] [DecidableEq J] (N : Mat J) (v : J → ℂ) :
    star v ⬝ᵥ (Nᴴ *ᵥ v) = star (star v ⬝ᵥ (N *ᵥ v)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.conjTranspose_apply, Pi.star_apply, Finset.mul_sum,
    star_sum, star_mul', star_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma S169H_cs (A : Alg I) (Phi : MatrixMap I J) (c : ℝ) (hc : SchwarzBound A Phi c)
    (a b : Mat I) (ha : a ∈ A) (hb : b ∈ A)
    (h0 : (c : ℂ) • Phi (aᴴ * a) - (Phi a)ᴴ * Phi a = 0) :
    (c : ℂ) • Phi (bᴴ * a) - (Phi b)ᴴ * Phi a = 0 := by
  set M : Mat I → Mat I → Mat J := fun x y => (c : ℂ) • Phi (xᴴ * y) - (Phi x)ᴴ * Phi y with hM
  have hpos : ∀ x ∈ A, (M x x).PosSemidef := fun x hx => hc.2.2 x hx
  have hmemS : ∀ x ∈ A, xᴴ ∈ A := fun x hx => by
    rw [← Matrix.star_eq_conjTranspose]; exact star_mem hx
  have hadj : (M a b)ᴴ = M b a := by
    simp only [hM, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Complex.star_def, Complex.conj_ofReal]
    rw [← S169H_herm A Phi hc.2.1 _ (A.mul_mem (hmemS a ha) hb)]
    simp [Matrix.conjTranspose_mul]
  have hexp : ∀ t : ℂ, M (a + t • b) (a + t • b) =
      M a a + t • M a b + star t • M b a + (star t * t) • M b b := by
    intro t
    simp only [hM, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, map_add, map_smul, smul_smul]
    module
  have hβ : ∀ v : J → ℂ, star v ⬝ᵥ (M b a *ᵥ v) = 0 := by
    intro v
    set β := star v ⬝ᵥ (M b a *ᵥ v)
    set γ := star v ⬝ᵥ (M b b *ᵥ v)
    have hγ := Complex.nonneg_iff.mp ((hpos b hb).dotProduct_mulVec_nonneg v)
    have hab : star v ⬝ᵥ (M a b *ᵥ v) = star β := by
      rw [show M a b = (M b a)ᴴ by rw [← hadj, Matrix.conjTranspose_conjTranspose], S169H_dot_adj]
    set s : ℝ := 1 / (γ.re + 1)
    have hs : 0 < s := div_pos one_pos (by linarith [hγ.1])
    have hsγ : s * γ.re < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by linarith [hγ.1])]; linarith
    have key := Complex.nonneg_iff.mp
      ((hpos _ (A.add_mem ha (A.smul_mem hb (-(s : ℂ) * β)))).dotProduct_mulVec_nonneg v)
    rw [hexp, show M a a = 0 from h0] at key
    simp only [zero_add, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, hab] at key
    have hn : 0 ≤ Complex.normSq β := Complex.normSq_nonneg _
    have e1 : (-(s : ℂ) * β * star β +
        star (-(s : ℂ) * β) * β + star (-(s : ℂ) * β) * (-(s : ℂ) * β) * γ).re =
        Complex.normSq β * (s * (s * γ.re - 2)) := by
      have hγi : γ.im = 0 := hγ.2.symm
      simp only [star_mul', star_neg, Complex.star_def, Complex.conj_ofReal]
      simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply, hγi]
      ring
    have := key.1
    rw [show star v ⬝ᵥ (M b a *ᵥ v) = β from rfl] at this
    rw [e1] at this
    have h2 : s * (s * γ.re - 2) < 0 := mul_neg_of_pos_of_neg hs (by linarith)
    have : Complex.normSq β = 0 := by nlinarith
    exact Complex.normSq_eq_zero.mp this
  exact S169H_quad_zero _ hβ

theorem S169H_main [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : AlgebraSchwarzMap A Phi) :
    let c := (snorm A Phi).toReal
    let D := {X : Mat I | X ∈ A ∧ Phi X * Phi (Xᴴ) = (c : ℂ) • Phi (X * Xᴴ)}
    (∀ X ∈ A, X ∈ D ↔ ∀ Z ∈ A, Phi X * Phi Z = (c : ℂ) • Phi (X * Z)) ∧
    (0 : Mat I) ∈ D ∧
    (∀ X ∈ D, ∀ Y ∈ D, X + Y ∈ D) ∧
    (∀ a : ℂ, ∀ X ∈ D, a • X ∈ D) ∧
    (∀ X ∈ D, ∀ Y ∈ D, X * Y ∈ D) := by
  intro c D
  have hv := S169H_valid A Phi hp
  have hpos := hv.2.1
  have hmemS : ∀ x ∈ A, xᴴ ∈ A := fun x hx => by
    rw [← Matrix.star_eq_conjTranspose]; exact star_mem hx
  have hchar : ∀ X ∈ A, X ∈ D ↔ ∀ Z ∈ A, Phi X * Phi Z = (c : ℂ) • Phi (X * Z) := by
    intro X hX
    constructor
    · rintro ⟨-, hD⟩ Z hZ
      have h0 : (c : ℂ) • Phi ((Xᴴ)ᴴ * Xᴴ) - (Phi Xᴴ)ᴴ * Phi Xᴴ = 0 := by
        rw [Matrix.conjTranspose_conjTranspose, S169H_herm A Phi hpos X hX,
          Matrix.conjTranspose_conjTranspose, ← S169H_herm A Phi hpos X hX, hD, sub_self]
      have h1 := S169H_cs A Phi c hv Xᴴ Z (hmemS X hX) hZ h0
      have h2 := congrArg Matrix.conjTranspose h1
      rw [Matrix.conjTranspose_zero, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        ← S169H_herm A Phi hpos _ (A.mul_mem (hmemS Z hZ) (hmemS X hX)), Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
        S169H_herm A Phi hpos X hX, Matrix.conjTranspose_conjTranspose, Complex.star_def,
        Complex.conj_ofReal] at h2
      exact (sub_eq_zero.mp h2).symm
    · intro h
      exact ⟨hX, h _ (hmemS X hX)⟩
  refine ⟨hchar, ⟨A.zero_mem, by simp⟩, ?_, ?_, ?_⟩
  · intro X hX Y hY
    have hXY := A.add_mem hX.1 hY.1
    refine (hchar _ hXY).mpr fun Z hZ => ?_
    rw [map_add, Matrix.add_mul, (hchar X hX.1).mp hX Z hZ, (hchar Y hY.1).mp hY Z hZ,
      Matrix.add_mul, map_add, smul_add]
  · intro a X hX
    have haX := A.smul_mem hX.1 a
    refine (hchar _ haX).mpr fun Z hZ => ?_
    rw [map_smul, Matrix.smul_mul, (hchar X hX.1).mp hX Z hZ, Matrix.smul_mul, map_smul, smul_comm]
  · intro X hX Y hY
    have hXY := A.mul_mem hX.1 hY.1
    refine (hchar _ hXY).mpr fun Z hZ => ?_
    have e1 := (hchar X hX.1).mp hX Y hY.1
    have e2 := (hchar X hX.1).mp hX (Y * Z) (A.mul_mem hY.1 hZ)
    have e3 := (hchar Y hY.1).mp hY Z hZ
    by_cases hc0 : (c : ℂ) = 0
    · have hz : ∀ W ∈ A, Phi W = 0 := by
        intro W hW
        have h3 : ((((snorm A Phi).toReal : ℂ)) • Phi (Wᴴ * W) - (Phi W)ᴴ * Phi W).PosSemidef :=
          hv.2.2 W hW
        rw [show (((snorm A Phi).toReal : ℂ)) = 0 from hc0, zero_smul, zero_sub] at h3
        have h4 := Matrix.posSemidef_conjTranspose_mul_self (Phi W)
        have h5 : (Phi W)ᴴ * Phi W = 0 := by
          apply S169H_quad_zero
          intro v
          have a1 := h3.dotProduct_mulVec_nonneg v
          rw [Matrix.neg_mulVec, dotProduct_neg] at a1
          exact le_antisymm (neg_nonneg.mp a1) (h4.dotProduct_mulVec_nonneg v)
        exact Matrix.conjTranspose_mul_self_eq_zero.mp h5
      rw [hz _ hXY, hc0, zero_smul, Matrix.zero_mul]
    · have key : (c : ℂ) • (Phi (X * Y) * Phi Z) = (c : ℂ) • ((c : ℂ) • Phi (X * Y * Z)) := by
        calc (c : ℂ) • (Phi (X * Y) * Phi Z) = ((c : ℂ) • Phi (X * Y)) * Phi Z :=
              (Matrix.smul_mul _ _ _).symm
          _ = (Phi X * Phi Y) * Phi Z := by rw [e1]
          _ = Phi X * (Phi Y * Phi Z) := Matrix.mul_assoc _ _ _
          _ = Phi X * ((c : ℂ) • Phi (Y * Z)) := by rw [e3]
          _ = (c : ℂ) • (Phi X * Phi (Y * Z)) := Matrix.mul_smul _ _ _
          _ = (c : ℂ) • ((c : ℂ) • Phi (X * (Y * Z))) := by rw [e2]
          _ = (c : ℂ) • ((c : ℂ) • Phi (X * Y * Z)) := by rw [Matrix.mul_assoc]
      exact smul_right_injective (Mat J) hc0 key

end QAlgorithms.Papers.Independent.Support50.P12

end

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Support50.P12
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : AlgebraSchwarzMap A Phi) :
    let c := (snorm A Phi).toReal
    let D := {X : Mat I | X ∈ A ∧ Phi X * Phi (Xᴴ) = (c : ℂ) • Phi (X * Xᴴ)}
    (∀ X ∈ A, X ∈ D ↔ ∀ Z ∈ A, Phi X * Phi Z = (c : ℂ) • Phi (X * Z)) ∧
    (0 : Mat I) ∈ D ∧
    (∀ X ∈ D, ∀ Y ∈ D, X + Y ∈ D) ∧
    (∀ a : ℂ, ∀ X ∈ D, a • X ∈ D) ∧
    (∀ X ∈ D, ∀ Y ∈ D, X * Y ∈ D) :=
  S169H_main A B Phi hc hp
