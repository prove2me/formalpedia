-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P29.polarPartialIsometry_replacement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:32:16.593143+00:00
-- url     : https://prove2.me/submissions/35027336-ff3a-4755-8314-802d3d4d609e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace X7pi

open scoped Matrix ComplexConjugate InnerProductSpace ComplexOrder

/-- column inner product as Euclidean inner product -/
theorem cs {I : Type*} [Fintype I] (a y : I → ℂ) :
    ‖∑ i, conj (a i) * y i‖ ≤ Real.sqrt (∑ i, Complex.normSq (a i)) * Real.sqrt (∑ i, Complex.normSq (y i)) := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a : EuclideanSpace ℂ I) (WithLp.toLp 2 y)
  have e1 : ⟪(WithLp.toLp 2 a : EuclideanSpace ℂ I), WithLp.toLp 2 y⟫_ℂ = ∑ i, conj (a i) * y i := by
    rw [EuclideanSpace.inner_toLp_toLp]; simp [dotProduct, mul_comm]
  have e2 : ∀ x : I → ℂ, ‖(WithLp.toLp 2 x : EuclideanSpace ℂ I)‖ = Real.sqrt (∑ i, Complex.normSq (x i)) := by
    intro x; rw [EuclideanSpace.norm_eq]; simp [Complex.sq_norm]
  rw [e1, e2, e2] at h; exact h

theorem colsum {I J : Type*} [Fintype I] (M N : Matrix I J ℂ) (j k : J) :
    (Mᴴ * N) j k = ∑ i, conj (M i j) * N i k := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem core {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (X A : Matrix I J ℂ) (hA : (1 - Aᴴ * A).PosSemidef) (hcard : Fintype.card J ≤ Fintype.card I) :
    ∃ W : Matrix J I ℂ, W * Wᴴ = 1 ∧ ‖(Aᴴ * X).trace‖ ≤ ‖(W * X).trace‖ := by
  have hH : (Xᴴ * X).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self X
  set V : Matrix J J ℂ := (hH.eigenvectorUnitary : Matrix J J ℂ) with hVdef
  have hV1 : Vᴴ * V = 1 := Unitary.coe_star_mul_self _
  have hV2 : V * Vᴴ = 1 := Unitary.coe_mul_star_self _
  set lam : J → ℝ := hH.eigenvalues with hlamdef
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => (Matrix.posSemidef_conjTranspose_mul_self X).eigenvalues_nonneg j
  set Y : Matrix I J ℂ := X * V with hYdef
  have hYY : Yᴴ * Y = Matrix.diagonal (fun j => (lam j : ℂ)) := by
    have hs := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    have e : Yᴴ * Y = Vᴴ * (Xᴴ * X) * V := by
      simp only [hYdef, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e, hs]
    simp only [Matrix.mul_assoc]
    rw [show star (hH.eigenvectorUnitary : Matrix J J ℂ) = Vᴴ from rfl, ← hVdef, hV1, Matrix.mul_one,
      ← Matrix.mul_assoc, hV1, Matrix.one_mul]
    rfl
  have hcol : ∀ j k, ∑ i, conj (Y i j) * Y i k = if j = k then (lam j : ℂ) else 0 := by
    intro j k
    rw [← colsum, hYY, Matrix.diagonal_apply]
  have hnormY : ∀ j, ∑ i, Complex.normSq (Y i j) = lam j := by
    intro j
    apply Complex.ofReal_injective
    have := hcol j j
    rw [if_pos rfl] at this
    rw [← this]; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
  -- orthonormal extension
  let ι := J ⊕ Fin (Fintype.card I - Fintype.card J)
  have hcardeq : Module.finrank ℂ (EuclideanSpace ℂ I) = Fintype.card ι := by
    simp only [finrank_euclideanSpace, ι, Fintype.card_sum, Fintype.card_fin]; omega
  let c : J → ℂ := fun j => ((Real.sqrt (lam j))⁻¹ : ℝ)
  let v' : ι → EuclideanSpace ℂ I :=
    Sum.elim (fun j => WithLp.toLp 2 (fun i => c j * Y i j)) 0
  let s : Set ι := Sum.inl '' {j | lam j ≠ 0}
  have hon : Orthonormal ℂ (s.restrict v') := by
    rw [orthonormal_iff_ite]
    have hv : ∀ j, v' (Sum.inl j) = WithLp.toLp 2 (fun i => c j * Y i j) := fun j => rfl
    intro x y
    change ⟪v' x.1, v' y.1⟫_ℂ = if x = y then 1 else 0
    have hx : x.1 ∈ s := x.2
    have hy : y.1 ∈ s := y.2
    obtain ⟨j, hj, hxj⟩ := hx
    obtain ⟨k, hk, hyk⟩ := hy
    have hxy : x = y ↔ j = k := by rw [Subtype.ext_iff, ← hxj, ← hyk, Sum.inl.inj_iff]
    rw [← hxj, ← hyk, if_congr hxy rfl rfl]
    simp only [hv, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply, RCLike.star_def, map_mul]
    have e : ∑ i, c k * Y i k * (conj (c j) * conj (Y i j)) = conj (c j) * c k *
        ∑ i, conj (Y i j) * Y i k := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [e, hcol]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, if_pos rfl]
      have hj' : lam j ≠ 0 := hj
      have hpos : 0 < lam j := lt_of_le_of_ne (hlam0 j) (Ne.symm hj')
      have hsq : Real.sqrt (lam j) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      have h1 := Real.mul_self_sqrt (hlam0 j)
      have hreal : (Real.sqrt (lam j))⁻¹ * (Real.sqrt (lam j))⁻¹ * lam j = 1 := by
        have h2 := Real.sq_sqrt (hlam0 j)
        field_simp; linarith
      simp only [c, Complex.conj_ofReal]
      exact_mod_cast hreal
    · rw [if_neg hjk, if_neg hjk]; simp
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcardeq hon
  let Z : Matrix I J ℂ := Matrix.of fun i j => b (Sum.inl j) i
  have hZ : Zᴴ * Z = 1 := by
    ext j k
    rw [colsum]
    have := (orthonormal_iff_ite.mp b.orthonormal) (Sum.inl j) (Sum.inl k)
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    show ∑ i, conj (b (Sum.inl j) i) * b (Sum.inl k) i = (1 : Matrix J J ℂ) j k
    have h2 : (if j = k then (1:ℂ) else 0) = if (Sum.inl j : ι) = Sum.inl k then 1 else 0 := by
      by_cases h : j = k <;> simp [h]
    rw [Matrix.one_apply, h2]
    rw [← this]
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => by ring
  refine ⟨V * Zᴴ, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Zᴴ, hZ, Matrix.one_mul, hV2]
  -- traces
  have htrW : (V * Zᴴ * X).trace = ((∑ j, Real.sqrt (lam j) : ℝ) : ℂ) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← hYdef, Matrix.trace]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag, colsum]
    by_cases hj : lam j = 0
    · have hY0 : ∀ i, Y i j = 0 := by
        intro i
        have h1 := hnormY j
        rw [hj] at h1
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (Y i j))).mp h1 i
          (Finset.mem_univ _)
        exact Complex.normSq_eq_zero.mp this
      simp [hY0, hj]
    · have hbj := hb (Sum.inl j) ⟨j, hj, rfl⟩
      simp only [Z, Matrix.of_apply, hbj]
      have e : ∑ i, conj ((v' (Sum.inl j)) i) * Y i j = conj (c j) * ∑ i, conj (Y i j) * Y i j := by
        simp only [v', Sum.elim_inl, PiLp.toLp_apply, map_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [e, hcol, if_pos rfl]
      simp only [c, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      have hpos : 0 < lam j := lt_of_le_of_ne (hlam0 j) (Ne.symm hj)
      have hsq : Real.sqrt (lam j) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
      have := Real.mul_self_sqrt (hlam0 j)
      field_simp
      linarith
  rw [htrW, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => Real.sqrt_nonneg _)]
  -- bound tr(Aᴴ X)
  have hAX : (Aᴴ * X).trace = ∑ j, ∑ i, conj ((A * V) i j) * Y i j := by
    have : Aᴴ * X = Aᴴ * X * V * Vᴴ := by rw [Matrix.mul_assoc _ V, hV2, Matrix.mul_one]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [show Vᴴ * Aᴴ = (A * V)ᴴ from (Matrix.conjTranspose_mul A V).symm, Matrix.mul_assoc, ← hYdef,
      Matrix.trace]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag, colsum]
  have hAV : ∀ j, ∑ i, Complex.normSq ((A * V) i j) ≤ 1 := by
    intro j
    have hP := hA.conjTranspose_mul_mul_same V
    have hd := hP.diag_nonneg (i := j)
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV1, ← Matrix.mul_assoc, Matrix.mul_assoc _ A,
      show Vᴴ * Aᴴ = (A * V)ᴴ from (Matrix.conjTranspose_mul A V).symm, Matrix.sub_apply,
      Matrix.one_apply_eq, colsum] at hd
    have hre := (Complex.nonneg_iff.mp hd).1
    simp only [Complex.sub_re, Complex.one_re, Complex.re_sum] at hre
    have : ∀ i, (conj ((A * V) i j) * (A * V) i j).re = Complex.normSq ((A * V) i j) := by
      intro i; rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    simp only [this] at hre
    linarith
  rw [hAX]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  refine le_trans (cs _ _) ?_
  rw [hnormY]
  calc Real.sqrt (∑ i, Complex.normSq ((A * V) i j)) * Real.sqrt (lam j) ≤ 1 * Real.sqrt (lam j) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr (hAV j)) (Real.sqrt_nonneg _)
    _ = _ := one_mul _

end X7pi

end

noncomputable section

namespace X7pi

open scoped Matrix ComplexConjugate InnerProductSpace ComplexOrder

theorem nrm {I : Type*} [Fintype I] (v : I → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  push_cast
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.normSq_eq_conj_mul_self]

theorem adjdot {I J : Type*} [Fintype I] [Fintype J] (M : Matrix I J ℂ) (v : J → ℂ) (w : I → ℂ) :
    star (M *ᵥ v) ⬝ᵥ w = star v ⬝ᵥ (Mᴴ *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]

theorem adj_contr {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (A : Matrix I J ℂ) (hA : (1 - Aᴴ * A).PosSemidef) : (1 - A * Aᴴ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  set z := Aᴴ *ᵥ x with hzdef
  have hzz : star z ⬝ᵥ z = star x ⬝ᵥ (A *ᵥ z) := by
    have := adjdot Aᴴ x z
    rw [Matrix.conjTranspose_conjTranspose] at this
    exact this
  have e1 : star x ⬝ᵥ ((1 - A * Aᴴ) *ᵥ x) = star x ⬝ᵥ x - star z ⬝ᵥ z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, hzz]
  have hz : star z ⬝ᵥ ((1 - Aᴴ * A) *ᵥ z) = star z ⬝ᵥ z - star (A *ᵥ z) ⬝ᵥ (A *ᵥ z) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← adjdot A z (A *ᵥ z)]
  have h0 := hA.dotProduct_mulVec_nonneg z
  rw [hz, nrm, nrm, ← Complex.ofReal_sub, Complex.zero_le_real] at h0
  have hcs := cs x (A *ᵥ z)
  have e2 : ∑ i, conj (x i) * (A *ᵥ z) i = star x ⬝ᵥ (A *ᵥ z) := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  rw [e2, ← hzz, nrm, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
    Complex.normSq_nonneg _)] at hcs
  rw [e1, nrm, nrm, ← Complex.ofReal_sub, Complex.zero_le_real]
  set a := ∑ i, Complex.normSq (x i)
  set b := ∑ i, Complex.normSq (z i)
  set c := ∑ i, Complex.normSq ((A *ᵥ z) i)
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hb : 0 ≤ b := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hsc : Real.sqrt c ≤ Real.sqrt b := Real.sqrt_le_sqrt (by linarith)
  have hb' : b = Real.sqrt b * Real.sqrt b := (Real.mul_self_sqrt hb).symm
  have ha' : a = Real.sqrt a * Real.sqrt a := (Real.mul_self_sqrt ha).symm
  have h3 : Real.sqrt b * Real.sqrt b ≤ Real.sqrt a * Real.sqrt b := by
    calc _ = b := hb'.symm
      _ ≤ Real.sqrt a * Real.sqrt c := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left hsc (Real.sqrt_nonneg _)
  have h4 : Real.sqrt b ≤ Real.sqrt a := by
    rcases (Real.sqrt_nonneg b).lt_or_eq with h | h
    · exact le_of_mul_le_mul_right h3 h
    · rw [← h]; exact Real.sqrt_nonneg _
  have := mul_le_mul h4 h4 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  linarith

theorem core2 {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (X A : Matrix I J ℂ) (hA : (1 - Aᴴ * A).PosSemidef) :
    ∃ W : Matrix J I ℂ, (W * Wᴴ = 1 ∨ Wᴴ * W = 1) ∧ ‖(Aᴴ * X).trace‖ ≤ ‖(W * X).trace‖ := by
  rcases le_or_gt (Fintype.card J) (Fintype.card I) with h | h
  · obtain ⟨W, hW, hle⟩ := core X A hA h
    exact ⟨W, Or.inl hW, hle⟩
  · have hA' : (1 - Aᴴᴴ * Aᴴ).PosSemidef := by
      rw [Matrix.conjTranspose_conjTranspose]; exact adj_contr A hA
    obtain ⟨W, hW, hle⟩ := core Xᴴ Aᴴ hA' h.le
    refine ⟨Wᴴ, Or.inr (by rw [Matrix.conjTranspose_conjTranspose]; exact hW), ?_⟩
    rw [Matrix.conjTranspose_conjTranspose] at hle
    have e1 : ‖(Aᴴ * X).trace‖ = ‖(A * Xᴴ).trace‖ := by
      rw [← Matrix.conjTranspose_conjTranspose (Aᴴ * X), Matrix.trace_conjTranspose, norm_star,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
    have e2 : ‖(Wᴴ * X).trace‖ = ‖(W * Xᴴ).trace‖ := by
      rw [← Matrix.conjTranspose_conjTranspose (Wᴴ * X), Matrix.trace_conjTranspose, norm_star,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
    rw [e1, e2]; exact hle

theorem trcs {K L : Type*} [Fintype K] [Fintype L] (P : Matrix K L ℂ) (Q : Matrix L K ℂ) :
    ‖(P * Q).trace‖ ≤ Real.sqrt (∑ k, ∑ l, Complex.normSq (P k l)) *
      Real.sqrt (∑ l, ∑ k, Complex.normSq (Q l k)) := by
  have h := cs (I := K × L) (fun x => conj (P x.1 x.2)) (fun x => Q x.2 x.1)
  simp only [Complex.conj_conj, Complex.normSq_conj, Fintype.sum_prod_type] at h
  rw [Finset.sum_comm (f := fun l k => Complex.normSq (Q l k))]
  refine le_of_eq_of_le ?_ h
  simp [Matrix.trace, Matrix.mul_apply]

theorem frob {K L : Type*} [Fintype K] [Fintype L] (Q : Matrix L K ℂ) :
    ((∑ l, ∑ k, Complex.normSq (Q l k) : ℝ) : ℂ) = (Q * Qᴴ).trace := by
  push_cast
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    Complex.normSq_eq_conj_mul_self]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

end X7pi

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

theorem X7pi_main {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (E : Matrix J I ℂ) (A : Matrix I J ℂ) (eta : ℝ)
    (hgood : 1 - eta ≤ operatorFe rho (A * E))
    (hcontract : (1 - Aᴴ * A).PosSemidef) (hnorm : (E * rho * Eᴴ).trace = 1) :
    ∃ W : Matrix J I ℂ, IsMaximalPartialIsometry W ∧
      1 - 2 * eta ≤ operatorFe rho (A * W) := by
  have hH : rho.IsHermitian := hrho.1.isHermitian
  set U : Matrix I I ℂ := (hH.eigenvectorUnitary : Matrix I I ℂ) with hUdef
  set p : I → ℝ := hH.eigenvalues with hpdef
  have hspec : rho = U * Matrix.diagonal (fun i => (p i : ℂ)) * Uᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hp0 : ∀ i, 0 ≤ p i := fun i => hrho.1.eigenvalues_nonneg i
  set R : Matrix I I ℂ := U * Matrix.diagonal (fun i => ((Real.sqrt (p i) : ℝ) : ℂ)) with hRdef
  have hR : R * Rᴴ = rho := by
    rw [hspec, hRdef, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal, ← Matrix.mul_assoc]
    congr 3
    funext i
    simp only [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hp0 i)]
  set P : Matrix I J ℂ := Rᴴ * A with hPdef
  set τ : ℝ := ∑ k, ∑ l, Complex.normSq (P k l) with hτdef
  have hτ0 : 0 ≤ τ := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _
  -- tr(Aᴴ ρ A) = τ
  have hτ : (Aᴴ * (rho * A)).trace = (τ : ℂ) := by
    rw [hτdef, X7pi.frob P, ← hR, hPdef]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm Rᴴ]; simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm A]; simp only [Matrix.mul_assoc]
  -- Cauchy-Schwarz
  have hCS : Complex.normSq ((A * E) * rho).trace ≤ τ := by
    have h := X7pi.trcs P (E * R)
    have e1 : ((A * E) * rho).trace = (P * (E * R)).trace := by
      rw [← hR, hPdef, Matrix.trace_mul_comm, Matrix.mul_assoc]
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm R]; simp only [Matrix.mul_assoc]
    have e2 : ∑ l, ∑ k, Complex.normSq ((E * R) l k) = 1 := by
      apply Complex.ofReal_injective
      rw [X7pi.frob]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R, hR, ← Matrix.mul_assoc, hnorm, Complex.ofReal_one]
    rw [e2, Real.sqrt_one, mul_one, ← e1] at h
    rw [Complex.normSq_eq_norm_sq]
    have := Real.sq_sqrt hτ0
    nlinarith [norm_nonneg ((A * E * rho).trace), Real.sqrt_nonneg τ]
  obtain ⟨W, hW, hle⟩ := X7pi.core2 (rho * A) A hcontract
  refine ⟨W, ⟨?_, hW.symm⟩, ?_⟩
  · unfold IsPartialIsometry
    rcases hW with h | h
    · rw [h, Matrix.one_mul]
    · rw [Matrix.mul_assoc, h, Matrix.mul_one]
  · rw [hτ, Complex.norm_real, Real.norm_of_nonneg hτ0] at hle
    have e3 : ((A * W) * rho).trace = (W * (rho * A)).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    unfold operatorFe at hgood ⊢
    rw [e3, Complex.normSq_eq_norm_sq]
    have h1 : τ * τ ≤ ‖(W * (rho * A)).trace‖ ^ 2 := by nlinarith
    nlinarith [sq_nonneg (τ - 1), hCS, hgood, h1]

end QAlgorithms.Papers.Independent.Gap48.P29

end

open QAlgorithms.Papers.Independent.Gap48.P29 QAlgorithms in
open scoped Matrix ComplexOrder in
theorem solution {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho)
    (E : Matrix J I ℂ) (A : Matrix I J ℂ) (eta : ℝ)
    (hgood : 1 - eta ≤ operatorFe rho (A * E))
    (hcontract : (1 - Aᴴ * A).PosSemidef) (hnorm : (E * rho * Eᴴ).trace = 1) :
    ∃ W : Matrix J I ℂ, IsMaximalPartialIsometry W ∧
      1 - 2 * eta ≤ operatorFe rho (A * W) :=
  X7pi_main rho hrho E A eta hgood hcontract hnorm
