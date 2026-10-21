-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P45.represented_casimir_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T03:17:45.309273+00:00
-- url     : https://prove2.me/submissions/339c6aff-439a-4b2a-a098-8d5b70461e69

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45
noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

open QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable


theorem g65a_schur {d h : ℕ} (pi : SmoothUnitaryRep d h) (hirr : IsCloningRepresentationIrreducible pi)
    (C : Mat h) (hC : ∀ u : U d, (pi.action u : Mat h) * C = C * (pi.action u : Mat h)) :
    ∃ c : ℂ, C = c • (1 : Mat h) := by
  have hh : 0 < h := hirr.1
  have : Nontrivial (Fin h → ℂ) := by
    have : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
    infer_instance
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' C)
  refine ⟨c, ?_⟩
  set W := Module.End.eigenspace (Matrix.toLin' C) c with hW
  have hinv : ∀ u : U d, ∀ v ∈ W, Matrix.mulVec (pi.action u : Mat h) v ∈ W := by
    intro u v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    simp only [Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hC u, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  rcases hirr.2 W hinv with h0 | htop
  · exact absurd h0 hc
  · ext i j
    have hv : Pi.single j (1:ℂ) ∈ W := htop ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv
    have := congrFun hv i
    have e : (C *ᵥ Pi.single j (1:ℂ)) i = C i j := by simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e] at this
    rw [this]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]

open NormedSpace in
theorem g65a_expcurve {d : ℕ} (X : Mat d) (hX : Xᴴ = -X) :
    ∃ u : ℝ → U d, u 0 = 1 ∧ ∀ i j, HasDerivAt (fun t => (u t : Mat d) i j) (X i j) 0 := by
  letI : NormedRing (Mat d) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat d) := Matrix.linftyOpNormedAlgebra
  have hmem : ∀ t : ℝ, exp ((t : ℝ) • X) ∈ U d := by
    intro t
    rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hX]
    simp only [star_trivial, smul_neg]
    rw [Matrix.exp_neg]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
  refine ⟨fun t => ⟨exp (t • X), hmem t⟩, ?_, ?_⟩
  · ext i j; simp
  · intro i j
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    simp only [zero_smul, exp_zero, one_mul] at h
    have hl : HasDerivAt (fun t : ℝ => exp (t • X) i j) (X i j) 0 :=
      (Matrix.entryLinearMap ℝ ℂ i j : Mat d →ₗ[ℝ] ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) h
    exact hl

theorem g65a_deriv_conj {n : ℕ} (A B : Mat n) (F : ℝ → Mat n) (F' : Mat n)
    (h : ∀ i j, HasDerivAt (fun t => F t i j) (F' i j) 0) :
    ∀ i j, HasDerivAt (fun t => (A * F t * B) i j) ((A * F' * B) i j) 0 := by
  intro i j
  simp only [Matrix.mul_apply]
  apply HasDerivAt.fun_sum; intro a _
  apply HasDerivAt.mul_const
  apply HasDerivAt.fun_sum; intro b _
  exact (h b a).const_mul _

/-- conjugation equivariance of the differential on skew-Hermitian matrices -/
theorem g65a_conj_skew {d h : ℕ} (pi : SmoothUnitaryRep d h) (g : U d) (X : Mat d) (hX : Xᴴ = -X) :
    pi.differential ((g : Mat d) * X * (g : Mat d)ᴴ) =
      (pi.action g : Mat h) * pi.differential X * (pi.action g : Mat h)ᴴ := by
  obtain ⟨u, hu0, hu⟩ := g65a_expcurve X hX
  have h1 := pi.differential_spec (fun t => g * u t * g⁻¹) ((g : Mat d) * X * (g : Mat d)ᴴ)
    (by simp [hu0]) (by
      intro i j
      have := g65a_deriv_conj (g : Mat d) (g : Mat d)ᴴ (fun t => (u t : Mat d)) X hu i j
      simpa [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose] using this)
  have h2 := g65a_deriv_conj (pi.action g : Mat h) (pi.action g : Mat h)ᴴ
    (fun t => (pi.action (u t) : Mat h)) (pi.differential X)
    (pi.differential_spec u X hu0 hu)
  ext i j
  refine (h1 i j).unique ?_
  have e : (fun t => (pi.action (g * u t * g⁻¹) : Mat h) i j) =
      (fun t => ((pi.action g : Mat h) * (pi.action (u t) : Mat h) * (pi.action g : Mat h)ᴴ) i j) := by
    funext t
    simp [map_mul, map_inv, Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose]
  rw [e]; exact h2 i j

theorem g65f_lin_expand {d h : ℕ} (L : Mat d →ₗ[ℂ] Mat h) (Z : Mat d) :
    L Z = ∑ a : Fin d, ∑ b : Fin d, Z a b • L (Matrix.single a b 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← map_smul]; congr 1; ext i j; simp [Matrix.single_apply]

theorem g65f_lin_deriv {d h : ℕ} (L : Mat d →ₗ[ℂ] Mat h) (Z : ℝ → Mat d) (Z' : Mat d)
    (hZ : ∀ a b, HasDerivAt (fun t => Z t a b) (Z' a b) 0) :
    ∀ i j, HasDerivAt (fun t => L (Z t) i j) (L Z' i j) 0 := by
  intro i j
  have e : ∀ W : Mat d, L W i j = ∑ a : Fin d, ∑ b : Fin d, W a b * L (Matrix.single a b 1) i j := by
    intro W; rw [g65f_lin_expand L W]; simp [Matrix.sum_apply]
  rw [show (fun t => L (Z t) i j) = fun t => ∑ a : Fin d, ∑ b : Fin d, Z t a b * L (Matrix.single a b 1) i j
    from funext fun t => e (Z t), e Z']
  apply HasDerivAt.fun_sum; intro a _
  apply HasDerivAt.fun_sum; intro b _
  exact (hZ a b).mul_const _

theorem g65f_deriv_mul {n : ℕ} (F G : ℝ → Mat n) (F' G' : Mat n)
    (hF : ∀ i j, HasDerivAt (fun t => F t i j) (F' i j) 0)
    (hG : ∀ i j, HasDerivAt (fun t => G t i j) (G' i j) 0) :
    ∀ i j, HasDerivAt (fun t => (F t * G t) i j) ((F' * G 0 + F 0 * G') i j) 0 := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  apply HasDerivAt.fun_sum; intro a _
  exact (hF i a).mul (hG a j)

theorem g65f_decomp {d : ℕ} (X : Mat d) :
    ∃ A B : Mat d, Aᴴ = -A ∧ Bᴴ = -B ∧ X = A + Complex.I • B := by
  refine ⟨(1/2 : ℂ) • (X - Xᴴ), (-Complex.I/2) • (X + Xᴴ), ?_, ?_, ?_⟩
  · ext i j; simp [Matrix.conjTranspose_apply]; ring
  · ext i j; simp [Matrix.conjTranspose_apply]; ring
  · ext i j; simp; ring_nf; simp [Complex.I_sq]; ring

theorem g65f_conj {d h : ℕ} (pi : SmoothUnitaryRep d h) (g : U d) (X : Mat d) :
    pi.differential ((g : Mat d) * X * (g : Mat d)ᴴ) =
      (pi.action g : Mat h) * pi.differential X * (pi.action g : Mat h)ᴴ := by
  obtain ⟨A, B, hA, hB, rfl⟩ := g65f_decomp X
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add, map_smul,
    g65a_conj_skew pi g A hA, g65a_conj_skew pi g B hB]

theorem g65f_bracket_skew {d h : ℕ} (pi : SmoothUnitaryRep d h) (Y : Mat d) (hY : Yᴴ = -Y) (X : Mat d) :
    pi.differential (Y * X - X * Y) =
      pi.differential Y * pi.differential X - pi.differential X * pi.differential Y := by
  obtain ⟨u, hu0, hu⟩ := g65a_expcurve Y hY
  have hv0 : (u 0)⁻¹ = 1 := by simp [hu0]
  have hv : ∀ i j, HasDerivAt (fun t => ((u t)⁻¹ : U d) i j) ((-Y) i j) 0 := by
    intro i j
    have := (hu j i).star
    have e : (-Y) i j = star (Y j i) := by
      rw [← hY]; simp [Matrix.conjTranspose_apply]
    rw [e]
    have e2 : (fun t => ((u t)⁻¹ : U d) i j) = fun x => star ((u x : Mat d) j i) := by
      funext t
      simp [Matrix.UnitaryGroup.inv_val, Matrix.star_apply]
    rw [e2]; exact this
  -- LHS
  have hZ := g65f_deriv_mul (fun t => (u t : Mat d) * X) (fun t => ((u t)⁻¹ : U d)) (Y * X) (-Y)
    (by
      intro i j
      have := g65f_deriv_mul (fun t => (u t : Mat d)) (fun _ => X) Y 0 hu (fun _ _ => hasDerivAt_const _ _) i j
      simpa [hu0] using this) hv
  have hL := g65f_lin_deriv pi.differential _ _ hZ
  have hR1 := g65f_deriv_mul (fun t => (pi.action (u t) : Mat h) * pi.differential X)
    (fun t => (pi.action (u t)⁻¹ : Mat h)) (pi.differential Y * pi.differential X) (pi.differential (-Y))
    (by
      intro i j
      have := g65f_deriv_mul (fun t => (pi.action (u t) : Mat h)) (fun _ => pi.differential X) _ 0
        (pi.differential_spec u Y hu0 hu) (fun _ _ => hasDerivAt_const _ _) i j
      simpa [hu0] using this)
    (pi.differential_spec (fun t => (u t)⁻¹) (-Y) hv0 hv)
  ext i j
  have key : (fun t => pi.differential ((u t : Mat d) * X * ((u t)⁻¹ : U d)) i j) =
      (fun t => ((pi.action (u t) : Mat h) * pi.differential X * (pi.action (u t)⁻¹ : Mat h)) i j) := by
    funext t
    have := g65f_conj pi (u t) X
    rw [map_inv]
    simp only [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose] at this ⊢
    rw [this]
  have h1 := hL i j
  rw [key] at h1
  have := h1.unique (hR1 i j)
  simp [hu0, hv0, map_neg, Matrix.mul_neg] at this
  simpa [Matrix.mul_sub, sub_eq_add_neg] using this

theorem g65f_bracket {d h : ℕ} (pi : SmoothUnitaryRep d h) (Y X : Mat d) :
    pi.differential (Y * X - X * Y) =
      pi.differential Y * pi.differential X - pi.differential X * pi.differential Y := by
  obtain ⟨A, B, hA, hB, rfl⟩ := g65f_decomp Y
  have e : (A + Complex.I • B) * X - X * (A + Complex.I • B) = (A * X - X * A) + Complex.I • (B * X - X * B) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]; abel
  rw [e, map_add, map_smul, g65f_bracket_skew pi A hA, g65f_bracket_skew pi B hB, map_add, map_smul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]; abel

theorem g65f_unit {h : ℕ} (W : U h) : (W : Mat h)ᴴ * (W : Mat h) = 1 := by
  have := (Matrix.mem_unitaryGroup_iff').1 W.2
  simpa [Matrix.star_eq_conjTranspose] using this

theorem g65f_unit' {h : ℕ} (W : U h) : (W : Mat h) * (W : Mat h)ᴴ = 1 := by
  have := (Matrix.mem_unitaryGroup_iff).1 W.2
  simpa [Matrix.star_eq_conjTranspose] using this

theorem g65f_conj_single {d : ℕ} (g : Mat d) (j k : Fin d) (a b : Fin d) :
    (g * Matrix.single j k 1 * gᴴ : Mat d) a b = g a j * star (g b k) := by
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

theorem g65f_C2_inv {d h : ℕ} (pi : SmoothUnitaryRep d h) (g : U d) :
    (pi.action g : Mat h) * secondCasimir pi * (pi.action g : Mat h)ᴴ = secondCasimir pi := by
  have step : ∀ X Y : Mat d, (pi.action g : Mat h) * (pi.differential X * pi.differential Y) * (pi.action g : Mat h)ᴴ =
      pi.differential ((g : Mat d) * X * (g : Mat d)ᴴ) * pi.differential ((g : Mat d) * Y * (g : Mat d)ᴴ) := by
    intro X Y
    rw [g65f_conj, g65f_conj]
    have := g65f_unit (pi.action g)
    calc (pi.action g : Mat h) * (pi.differential X * pi.differential Y) * (pi.action g : Mat h)ᴴ
        = (pi.action g : Mat h) * pi.differential X * ((pi.action g : Mat h)ᴴ * (pi.action g : Mat h)) * pi.differential Y *
            (pi.action g : Mat h)ᴴ := by rw [this]; simp [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  unfold secondCasimir
  simp only [Finset.mul_sum, Finset.sum_mul, step]
  simp only [g65f_lin_expand pi.differential ((g : Mat d) * _ * (g : Mat d)ᴴ), g65f_conj_single]
  simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_smul_comm]
  have hc : ∀ a b c e : Fin d, ∑ j : Fin d, ∑ k : Fin d,
      (g a j * star (g b k) * (g c k * star (g e j))) = (1 : Mat d) a e * (1 : Mat d) c b := by
    intro a b c e
    rw [← g65f_unit' g]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have reorder : ∑ j : Fin d, ∑ k : Fin d, ∑ c : Fin d, ∑ e : Fin d, ∑ a : Fin d, ∑ b : Fin d,
      (g a j * star (g b k) * (g c k * star (g e j))) • (pi.differential (Matrix.single a b 1) * pi.differential (Matrix.single c e 1)) =
      ∑ a : Fin d, ∑ b : Fin d, ∑ c : Fin d, ∑ e : Fin d, (∑ j : Fin d, ∑ k : Fin d,
      (g a j * star (g b k) * (g c k * star (g e j)))) • (pi.differential (Matrix.single a b 1) * pi.differential (Matrix.single c e 1)) := by
    simp only [Finset.sum_smul]
    simp only [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.mk (fun x => (x.2.2.2.2.1, x.2.2.2.2.2, x.2.2.1, x.2.2.2.1, x.1, x.2.1))
      (fun y => (y.2.2.2.2.1, y.2.2.2.2.2, y.2.2.1, y.2.2.2.1, y.1, y.2.1))
      (fun _ => rfl) (fun _ => rfl)) _ _ (fun x => ?_)
    obtain ⟨j, k, a, b, c, e⟩ := x
    rfl
  rw [reorder]
  simp only [hc, Matrix.one_apply, ite_mul, one_mul, zero_mul, ite_smul, one_smul, zero_smul]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem g65f_comm {h : ℕ} (W : U h) (C : Mat h) (hC : (W : Mat h) * C * (W : Mat h)ᴴ = C) :
    (W : Mat h) * C = C * (W : Mat h) := by
  calc (W : Mat h) * C = (W : Mat h) * C * ((W : Mat h)ᴴ * (W : Mat h)) := by rw [g65f_unit, Matrix.mul_one]
    _ = ((W : Mat h) * C * (W : Mat h)ᴴ) * (W : Mat h) := by simp only [Matrix.mul_assoc]
    _ = C * W := by rw [hC]

theorem g65f_C1 {d h : ℕ} (pi : SmoothUnitaryRep d h) : firstCasimir pi = pi.differential 1 := by
  unfold firstCasimir; rw [← Matrix.sum_single_one, map_sum]

theorem g65f_C1_inv {d h : ℕ} (pi : SmoothUnitaryRep d h) (g : U d) :
    (pi.action g : Mat h) * firstCasimir pi * (pi.action g : Mat h)ᴴ = firstCasimir pi := by
  rw [g65f_C1, ← g65f_conj, Matrix.mul_one, g65f_unit']

theorem g65f_term {d h : ℕ} (pi : SmoothUnitaryRep d h) (m : Fin d → ℤ) (v : Fin h → ℂ)
    (hdiag : ∀ j, Matrix.mulVec (pi.differential (Matrix.single j j 1)) v = (m j : ℂ) • v)
    (hup : ∀ j k, j < k → Matrix.mulVec (pi.differential (Matrix.single j k 1)) v = 0) (j k : Fin d) :
    (pi.differential (Matrix.single j k 1) * pi.differential (Matrix.single k j 1)) *ᵥ v =
      ((if j < k then ((m j : ℂ) - m k) else 0) + (if j = k then (m j : ℂ)^2 else 0)) • v := by
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · have hb := g65f_bracket pi (Matrix.single j k 1) (Matrix.single k j 1)
    rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, one_mul] at hb
    have e : pi.differential (Matrix.single j k 1) * pi.differential (Matrix.single k j 1) =
        pi.differential (Matrix.single k j 1) * pi.differential (Matrix.single j k 1) +
        (pi.differential (Matrix.single j j 1) - pi.differential (Matrix.single k k 1)) := by
      rw [← map_sub, hb]; abel
    rw [e, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hup j k hjk, Matrix.mulVec_zero, Matrix.sub_mulVec,
      hdiag, hdiag, if_pos hjk, if_neg (ne_of_lt hjk)]
    simp [sub_smul]
  · rw [← Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_smul, hdiag]
    simp [smul_smul, sq]
  · rw [← Matrix.mulVec_mulVec, hup k j hjk, Matrix.mulVec_zero, if_neg (not_lt.2 hjk.le),
      if_neg (ne_of_gt hjk)]
    simp

theorem g65f_alg {d : ℕ} (hd : 0 < d) (m : Fin d → ℤ) :
    casimirValue m = (1 / (d : ℝ)) *
      (((d : ℝ) - 1) * ∑ j : Fin d, (m j : ℝ)^2 -
        (∑ j : Fin d, ∑ k : Fin d, if j ≠ k then (m j : ℝ) * m k else 0) +
        (d : ℝ) * ∑ j : Fin d, ∑ k : Fin d, if j < k then (m j : ℝ) - m k else 0) := by
  have hsq : (∑ j : Fin d, (m j : ℝ))^2 = ∑ j : Fin d, (m j : ℝ)^2 +
      ∑ j : Fin d, ∑ k : Fin d, if j ≠ k then (m j : ℝ) * m k else 0 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ k, (m j : ℝ) * m k = (if j = k then (m j : ℝ) * m k else 0) + (if j ≠ k then (m j : ℝ) * m k else 0) := by
      intro k; split_ifs <;> simp_all
    rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib]
    simp [sq]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold casimirValue secondCasimirValue
  rw [hsq]
  field_simp
  ring

theorem g65f_main {d h : ℕ} (hd : 2 ≤ d)
    (pi : SmoothUnitaryRep d h) (m : Fin d → ℤ) (hm : HasHighestWeight pi m) :
    firstCasimir pi = (∑ j : Fin d, (m j : ℂ)) • (1 : Mat h) ∧
    secondCasimir pi = (secondCasimirValue m : ℂ) • (1 : Mat h) := by
  obtain ⟨hirr, _, v, hv0, hdiag, hup⟩ := hm
  obtain ⟨c1, hc1⟩ := g65a_schur pi hirr (firstCasimir pi) (fun u => g65f_comm _ _ (g65f_C1_inv pi u))
  obtain ⟨c2, hc2⟩ := g65a_schur pi hirr (secondCasimir pi) (fun u => g65f_comm _ _ (g65f_C2_inv pi u))
  constructor
  · rw [hc1]; congr 1
    have e1 : firstCasimir pi *ᵥ v = (∑ j : Fin d, (m j : ℂ)) • v := by
      unfold firstCasimir; rw [Matrix.sum_mulVec, Finset.sum_smul]; simp only [hdiag]
    rw [hc1, Matrix.smul_mulVec, Matrix.one_mulVec] at e1
    exact smul_left_injective ℂ hv0 e1
  · rw [hc2]; congr 1
    have e2 : secondCasimir pi *ᵥ v = (secondCasimirValue m : ℂ) • v := by
      unfold secondCasimir
      simp only [Matrix.sum_mulVec, g65f_term pi m v hdiag hup, ← Finset.sum_smul]
      congr 1
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      unfold secondCasimirValue
      push_cast
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
    rw [hc2, Matrix.smul_mulVec, Matrix.one_mulVec] at e2
    exact smul_left_injective ℂ hv0 e2

theorem g65f_part5 {d h : ℕ} (pi : SmoothUnitaryRep d h) (s : ℂ) (h1 : firstCasimir pi = s • (1 : Mat h)) :
    ∑ j : Fin d, ∑ k : Fin d,
      pi.differential (Matrix.single j k 1 - (if j = k then (1 / (d : ℂ)) else 0) • (1 : Mat d)) *
      pi.differential (Matrix.single k j 1 - (if k = j then (1 / (d : ℂ)) else 0) • (1 : Mat d)) =
    secondCasimir pi - (2 * s / d) • firstCasimir pi + ((d : ℂ) * (s / d) ^ 2) • (1 : Mat h) := by
  have hF : ∀ j k : Fin d, pi.differential (Matrix.single j k 1 - (if j = k then (1 / (d : ℂ)) else 0) • (1 : Mat d)) =
      pi.differential (Matrix.single j k 1) - (if j = k then s / d else 0) • (1 : Mat h) := by
    intro j k
    rw [map_sub, map_smul, ← g65f_C1, h1, smul_smul]
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  simp only [hF]
  have hexp : ∀ j k : Fin d, (pi.differential (Matrix.single j k 1) - (if j = k then s / d else 0) • (1 : Mat h)) *
      (pi.differential (Matrix.single k j 1) - (if k = j then s / d else 0) • (1 : Mat h)) =
      pi.differential (Matrix.single j k 1) * pi.differential (Matrix.single k j 1) -
      (if j = k then s / d else 0) • (pi.differential (Matrix.single j j 1) + pi.differential (Matrix.single j j 1)) +
      (if j = k then (s / d) ^ 2 else 0) • (1 : Mat h) := by
    intro j k
    by_cases hjk : j = k
    · subst hjk; simp only [if_true, sub_mul, mul_sub, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, smul_add]; rw [sq]; abel
    · simp [hjk, Ne.symm hjk]
  simp only [hexp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  unfold secondCasimir firstCasimir
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.smul_sum, Finset.sum_add_distrib]
  rw [← two_smul ℂ (∑ j : Fin d, pi.differential (Matrix.single j j 1)), smul_smul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [show s / (d:ℂ) * 2 = 2 * s / d by ring]

/-- PDF p.14 Eqs.(A6)–(A9): actual represented Casimir eigenvalues, correcting
C_1 to C_2 in A7. A9 is expressed in traceless matrix units
F_jk=E_jk-delta_jk I/d; its inconsistent dummy indices are eliminated. -/
theorem solution (d h : ℕ) (hd : 2 ≤ d)
    (pi : SmoothUnitaryRep d h) (m : Fin d → ℤ) (hm : HasHighestWeight pi m) :
    firstCasimir pi = (∑ j : Fin d, (m j : ℂ)) • (1 : Mat h) ∧
    secondCasimir pi = (secondCasimirValue m : ℂ) • (1 : Mat h) ∧
    specialCasimir pi = (casimirValue m : ℂ) • (1 : Mat h) ∧
    casimirValue m = (1 / (d : ℝ)) *
      (((d : ℝ) - 1) * ∑ j : Fin d, (m j : ℝ)^2 -
        (∑ j : Fin d, ∑ k : Fin d, if j ≠ k then (m j : ℝ) * m k else 0) +
        (d : ℝ) * ∑ j : Fin d, ∑ k : Fin d, if j < k then (m j : ℝ) - m k else 0) ∧
    specialCasimir pi = ∑ j : Fin d, ∑ k : Fin d,
      pi.differential (Matrix.single j k 1 - (if j = k then (1 / (d : ℂ)) else 0) • (1 : Mat d)) *
      pi.differential (Matrix.single k j 1 - (if k = j then (1 / (d : ℂ)) else 0) • (1 : Mat d)) := by
  obtain ⟨h1, h2⟩ := g65f_main hd pi m hm
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have h3 : specialCasimir pi = (casimirValue m : ℂ) • (1 : Mat h) := by
    unfold specialCasimir; rw [h1, h2]; unfold casimirValue; push_cast
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← sub_smul]
    congr 1; ring
  refine ⟨h1, h2, h3, g65f_alg (by omega) m, ?_⟩
  rw [g65f_part5 pi _ h1, h3, h2, h1]; unfold casimirValue; push_cast
  simp only [smul_smul, ← sub_smul, ← add_smul]
  congr 1; field_simp; ring

end
