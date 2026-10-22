-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P24.pi_distance_trace_variational
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:04:46.006346+00:00
-- url     : https://prove2.me/submissions/59276a3a-d06b-48a0-8115-32d742fe34d6

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P24
noncomputable section

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Gap48.P24

universe u v

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq


theorem g74i_bessel {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {I : Type*}
    (b : HilbertBasis I ℂ H) (x y : H) :
    (Summable fun i => ‖inner ℂ x (b i) * inner ℂ (b i) y‖) ∧
      ∑' i, ‖inner ℂ x (b i) * inner ℂ (b i) y‖ ≤ ‖x‖ * ‖y‖ := by
  have hpq : (2 : ENNReal).toReal.HolderConjugate (2 : ENNReal).toReal := by
    simpa using Real.HolderConjugate.two_two
  have h := lp.tsum_mul_le_mul_norm hpq (b.repr x) (b.repr y)
  simp only [HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map] at h
  have e : ∀ i, ‖inner ℂ x (b i) * inner ℂ (b i) y‖ = ‖inner ℂ (b i) x‖ * ‖inner ℂ (b i) y‖ := by
    intro i; rw [norm_mul, ← inner_conj_symm, Complex.norm_conj]
  simp only [e]
  exact h

theorem g74i_G {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {I : Type*}
    (b : HilbertBasis I ℂ H) (a c : ℕ → H) (hs : Summable fun r => ‖a r‖ * ‖c r‖) :
    HasSum (fun i => ∑' r, inner ℂ (a r) (b i) * inner ℂ (b i) (c r)) (∑' r, inner ℂ (a r) (c r)) := by
  let F : ℕ × I → ℂ := fun p => inner ℂ (a p.1) (b p.2) * inner ℂ (b p.2) (c p.1)
  have hF : Summable fun p => ‖F p‖ := by
    rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun r => (g74i_bessel b (a r) (c r)).1, ?_⟩
    refine Summable.of_nonneg_of_le (fun r => tsum_nonneg fun _ => norm_nonneg _)
      (fun r => (g74i_bessel b (a r) (c r)).2) hs
  have hF' : Summable F := hF.of_norm
  have hsw : Summable (F ∘ Prod.swap) := hF'.prod_symm
  have h1 : HasSum (fun i => ∑' r, F (r, i)) (∑' q, (F ∘ Prod.swap) q) :=
    hsw.hasSum.prod_fiberwise (fun i => (hsw.prod_factor i).hasSum)
  have h2 : ∑' q, (F ∘ Prod.swap) q = ∑' p, F p :=
    (Equiv.prodComm I ℕ).tsum_eq F
  have h3 : ∑' p, F p = ∑' r, inner ℂ (a r) (c r) := by
    rw [hF'.tsum_prod]
    exact tsum_congr fun r => b.tsum_inner_mul_inner (a r) (c r)
  rw [h2, h3] at h1
  exact h1

theorem g74i_nuc_summable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u v : ℕ → H) (hs : Summable fun r => ‖u r‖ * ‖v r‖) (x : H) :
    Summable fun r => inner ℂ (v r) x • u r := by
  refine Summable.of_norm_bounded (g := fun r => ‖x‖ * (‖u r‖ * ‖v r‖)) (hs.mul_left _) fun r => ?_
  rw [norm_smul]
  calc ‖inner ℂ (v r) x‖ * ‖u r‖ ≤ (‖v r‖ * ‖x‖) * ‖u r‖ := by
        gcongr; exact norm_inner_le_norm _ _
    _ = ‖x‖ * (‖u r‖ * ‖v r‖) := by ring

theorem g74i_TF {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {I : Type*}
    (b : HilbertBasis I ℂ H) (ρ : H →L[ℂ] H) (u v : ℕ → H)
    (hρ : QAlgorithms.Papers.Independent.Dependency50.P13.NuclearRepresentation ρ u v)
    (P Q : H →L[ℂ] H) :
    HasSum (fun i => inner ℂ (P (b i)) (ρ (Q (b i))))
      (∑' r, inner ℂ (Q.adjoint (v r)) (P.adjoint (u r))) := by
  obtain ⟨hs, hrep⟩ := hρ
  have hs' : Summable fun r => ‖Q.adjoint (v r)‖ * ‖P.adjoint (u r)‖ := by
    refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_)
      ((hs.mul_left (‖Q‖ * ‖P‖)))
    calc ‖Q.adjoint (v r)‖ * ‖P.adjoint (u r)‖ ≤ (‖Q.adjoint‖ * ‖v r‖) * (‖P.adjoint‖ * ‖u r‖) := by
          gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖Q‖ * ‖P‖ * (‖u r‖ * ‖v r‖) := by
          rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]; ring
  have := g74i_G b (fun r => Q.adjoint (v r)) (fun r => P.adjoint (u r)) hs'
  convert this using 1
  funext i
  rw [hrep]
  refine ((innerSL ℂ (P (b i))).map_tsum (g74i_nuc_summable u v hs _)).trans (tsum_congr fun r => ?_)
  rw [innerSL_apply_apply, inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right, mul_comm]

theorem g74i_UB {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {I : Type*}
    (b : HilbertBasis I ℂ H) (ρ : H →L[ℂ] H) (u v : ℕ → H)
    (hρ : QAlgorithms.Papers.Independent.Dependency50.P13.NuclearRepresentation ρ u v)
    (hpos : QAlgorithms.Papers.Independent.Dependency50.P13.IsPositive ρ)
    (htr : QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b ρ = 1)
    (V1 V2 : H →L[ℂ] K) :
    (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b (ρ.comp (V1.adjoint.comp V1))).re +
      (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b (ρ.comp (V2.adjoint.comp V2))).re -
      2 * (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b (ρ.comp (V1.adjoint.comp V2))).re
      ≤ ‖V1 - V2‖ ^ 2 := by
  let Φ : (H →L[ℂ] H) → ℂ := fun X => ∑' r, inner ℂ (v r) (X (u r))
  have hA : ∀ X : H →L[ℂ] H, HasSum (fun i => inner ℂ (b i) (ρ (X (b i)))) (Φ X) := by
    intro X
    have := g74i_TF b ρ u v hρ (ContinuousLinearMap.id ℂ H) X
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.adjoint_id] at this
    convert this using 1
    exact tsum_congr fun r => (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
  have htrX : ∀ X : H →L[ℂ] H,
      QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b (ρ.comp X) = Φ X :=
    fun X => (hA X).tsum_eq
  have hadd : ∀ X Y, Φ (X + Y) = Φ X + Φ Y := by
    intro X Y
    have h := hA (X + Y)
    have e : (fun i => inner ℂ (b i) (ρ ((X + Y) (b i)))) =
        fun i => inner ℂ (b i) (ρ (X (b i))) + inner ℂ (b i) (ρ (Y (b i))) := by
      funext i; simp [inner_add_right]
    rw [e] at h
    exact h.unique ((hA X).add (hA Y))
  have hsub : ∀ X Y, Φ (X - Y) = Φ X - Φ Y := by
    intro X Y
    have h := hA (X - Y)
    have e : (fun i => inner ℂ (b i) (ρ ((X - Y) (b i)))) =
        fun i => inner ℂ (b i) (ρ (X (b i))) - inner ℂ (b i) (ρ (Y (b i))) := by
      funext i; simp [inner_sub_right]
    rw [e] at h
    exact h.unique ((hA X).sub (hA Y))
  have hsmul : ∀ (c : ℂ) X, Φ (c • X) = c * Φ X := by
    intro c X
    have h := hA (c • X)
    have e : (fun i => inner ℂ (b i) (ρ ((c • X) (b i)))) =
        fun i => c * inner ℂ (b i) (ρ (X (b i))) := by
      funext i; simp [inner_smul_right]
    rw [e] at h
    exact h.unique ((hA X).mul_left c)
  have hconj : ∀ X : H →L[ℂ] H, Φ X.adjoint = (starRingEnd ℂ) (Φ X) := by
    intro X
    refine (hA X.adjoint).unique ?_
    have h2 := g74i_TF b ρ u v hρ X.adjoint (ContinuousLinearMap.id ℂ H)
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.adjoint_adjoint] at h2
    have h3 := (Complex.hasSum_conj' (f := fun i => inner ℂ (X.adjoint (b i)) (ρ (b i)))).mpr h2
    have e : (fun i => (starRingEnd ℂ) (inner ℂ (X.adjoint (b i)) (ρ (b i)))) =
        fun i => inner ℂ (b i) (ρ (X.adjoint (b i))) := by
      funext i
      have hsa : ρ.adjoint = ρ := hpos.1
      rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left ρ, hsa,
        ContinuousLinearMap.adjoint_inner_right]
    rw [e] at h3
    convert h3 using 2
  have hposΦ : ∀ S : H →L[ℂ] H, 0 ≤ (Φ (S.adjoint.comp S)).re := by
    intro S
    have h := g74i_TF b ρ u v hρ S.adjoint S.adjoint
    simp only [ContinuousLinearMap.adjoint_adjoint] at h
    have e : ∑' r, inner ℂ (S (v r)) (S (u r)) = Φ (S.adjoint.comp S) :=
      tsum_congr fun r => by
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [e] at h
    have hre := Complex.reCLM.hasSum h
    simp only [Complex.reCLM_apply] at hre
    exact hre.nonneg fun i => hpos.2 _
  set W := V1 - V2 with hWdef
  have hWW : W.adjoint.comp W = V1.adjoint.comp V1 + V2.adjoint.comp V2 - V1.adjoint.comp V2
      - (V1.adjoint.comp V2).adjoint := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hWdef, map_sub,
      ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_sub]
    abel
  have hsa : IsSelfAdjoint (W.adjoint.comp W) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  have hle := hsa.le_algebraMap_norm_self
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hle)
  have hS' : star S * S = S.adjoint.comp S := by
    rw [ContinuousLinearMap.star_eq_adjoint]; rfl
  have h1 := hposΦ S
  rw [← hS', ← hS, Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ), hsub,
    hsmul] at h1
  have hid : Φ 1 = 1 := by
    rw [← htr, ← htrX]; rfl
  rw [hid, mul_one] at h1
  simp only [Complex.sub_re, RCLike.ofReal_re, Complex.ofReal_re, sub_nonneg] at h1
  rw [ContinuousLinearMap.norm_adjoint_comp_self] at h1
  rw [htrX, htrX, htrX]
  have h2 : Φ (W.adjoint.comp W) = Φ (V1.adjoint.comp V1) + Φ (V2.adjoint.comp V2) -
      Φ (V1.adjoint.comp V2) - (starRingEnd ℂ) (Φ (V1.adjoint.comp V2)) := by
    rw [hWW, hsub, hsub, hadd, hconj]
  rw [h2] at h1
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re] at h1
  have h1' : (Φ (V1.adjoint.comp V1)).re + (Φ (V2.adjoint.comp V2)).re -
      (Φ (V1.adjoint.comp V2)).re - (Φ (V1.adjoint.comp V2)).re ≤ ‖W‖ * ‖W‖ := h1
  nlinarith [h1']

theorem g74i_act_one {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (R : RepresentationData A) (hR : IsRepresentation R) (z : R.K) : R.act 1 z = z := by
  obtain ⟨⟨pi, hpi⟩, hden⟩ := hR
  let L : R.K →L[ℂ] R.K := R.act 1 - ContinuousLinearMap.id ℂ R.K
  have hspan : Submodule.span ℂ {z : R.K | ∃ a : A, ∃ x : R.K, z = R.act a x} ≤
      LinearMap.ker (L : R.K →ₗ[ℂ] R.K) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, x, rfl⟩
    show R.act 1 (R.act a x) - R.act a x = 0
    rw [hpi, hpi, ← ContinuousLinearMap.mul_apply, ← map_mul, one_mul, sub_self]
  have hcl := Submodule.topologicalClosure_minimal _ hspan (L.isClosed_ker)
  rw [hden] at hcl
  have : L z = 0 := hcl Submodule.mem_top
  simpa [L, sub_eq_zero] using this

theorem g74i_T_one {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H : CompleteComplexHilbert.{u}) (T : A → (H →L[ℂ] H)) (R : RepresentationData A)
    (V : H →L[ℂ] R.K) (hV : V ∈ dilationFiber H T R) : T 1 = V.adjoint.comp V := by
  rw [hV.2 1]
  congr 1
  ext x
  exact g74i_act_one R hV.1 (V x)

theorem g74i_rank_one {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {I : Type*} (b : HilbertBasis I ℂ H) (x : H) (hx : ‖x‖ = 1) :
    ∃ ρ : QAlgorithms.Papers.Independent.Dependency50.P13.State b, ∀ X : H →L[ℂ] H,
      QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b (ρ.val.val.comp X) =
        inner ℂ x (X x) := by
  let ρ : H →L[ℂ] H := (innerSL ℂ x).smulRight x
  have hρ : ∀ y, ρ y = inner ℂ x y • x := fun y => rfl
  have htr : ∀ X : H →L[ℂ] H,
      QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b (ρ.comp X) = inner ℂ x (X x) := by
    intro X
    unfold QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace
    rw [← ContinuousLinearMap.adjoint_inner_left, ← b.tsum_inner_mul_inner]
    refine tsum_congr fun i => ?_
    rw [ContinuousLinearMap.comp_apply, hρ, inner_smul_right, ContinuousLinearMap.adjoint_inner_left]
  let uu : ℕ → H := fun r => if r = 0 then x else 0
  have hnuc : QAlgorithms.Papers.Independent.Dependency50.P13.NuclearRepresentation ρ uu uu := by
    refine ⟨?_, fun y => ?_⟩
    · apply summable_of_ne_finset_zero (s := {0})
      intro r hr
      simp at hr
      simp [uu, hr]
    · rw [tsum_eq_single 0]
      · simp [uu, hρ]
      · intro r hr; simp [uu, hr]
  refine ⟨⟨⟨ρ, uu, uu, hnuc⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩, htr⟩
  · show ρ.adjoint = ρ
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro a c
    rw [hρ, hρ, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
  · intro y
    show 0 ≤ (inner ℂ y (ρ y)).re
    rw [hρ, inner_smul_right, ← inner_conj_symm x y, mul_comm, Complex.mul_conj]
    simp only [Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  · show QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b ρ = 1
    have := htr (ContinuousLinearMap.id ℂ H)
    rw [ContinuousLinearMap.comp_id] at this
    rw [this, ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K, hx]
    simp

theorem g74i_KS {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Nontrivial H] {I : Type*}
    (b : HilbertBasis I ℂ H) (V1 V2 : H →L[ℂ] K) :
    sSup {q : ℝ | ∃ rho : QAlgorithms.Papers.Independent.Dependency50.P13.State b,
      q = (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp (V1.adjoint.comp V1))).re +
        (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp (V2.adjoint.comp V2))).re -
        2 * (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp (V1.adjoint.comp V2))).re} = ‖V1 - V2‖ ^ 2 := by
  set Q := {q : ℝ | ∃ rho : QAlgorithms.Papers.Independent.Dependency50.P13.State b,
      q = (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp (V1.adjoint.comp V1))).re +
        (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp (V2.adjoint.comp V2))).re -
        2 * (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp (V1.adjoint.comp V2))).re} with hQ
  have hub : ∀ q ∈ Q, q ≤ ‖V1 - V2‖ ^ 2 := by
    rintro _ ⟨rho, rfl⟩
    obtain ⟨u, v, hn⟩ := rho.val.property
    exact g74i_UB b _ u v hn rho.property.1 rho.property.2 V1 V2
  have hval : ∀ x : H, ‖x‖ = 1 → ‖(V1 - V2) x‖ ^ 2 ∈ Q := by
    intro x hx
    obtain ⟨ρ, hρ⟩ := g74i_rank_one b x hx
    refine ⟨ρ, ?_⟩
    rw [hρ, hρ, hρ]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [ContinuousLinearMap.sub_apply, norm_sub_sq (𝕜 := ℂ)]
    have e1 : (inner ℂ (V1 x) (V1 x)).re = ‖V1 x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    have e2 : (inner ℂ (V2 x) (V2 x)).re = ‖V2 x‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    simp only [RCLike.re_to_complex]
    rw [e1, e2]; ring
  obtain ⟨y0, hy0⟩ := exists_ne (0 : H)
  have hx0 := norm_smul_inv_norm (𝕜 := ℂ) hy0
  apply le_antisymm (csSup_le ⟨_, hval _ hx0⟩ hub)
  have hbdd : BddAbove Q := ⟨_, hub⟩
  have hs0 : 0 ≤ sSup Q := le_trans (sq_nonneg _) (le_csSup hbdd (hval _ hx0))
  have hW : ‖V1 - V2‖ ≤ Real.sqrt (sSup Q) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun y => ?_
    by_cases hy : y = 0
    · simp [hy]
    have hx := norm_smul_inv_norm (𝕜 := ℂ) hy
    have h1 : ‖(V1 - V2) ((‖y‖⁻¹ : ℂ) • y)‖ ≤ Real.sqrt (sSup Q) :=
      (Real.le_sqrt (norm_nonneg _) hs0).mpr (le_csSup hbdd (hval _ hx))
    have hy' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy
    have e : (V1 - V2) y = (‖y‖ : ℂ) • (V1 - V2) ((‖y‖⁻¹ : ℂ) • y) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ hy', one_smul]
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  calc ‖V1 - V2‖ ^ 2 ≤ Real.sqrt (sSup Q) ^ 2 := by gcongr
    _ = sSup Q := Real.sq_sqrt hs0

/-- Lemma 4, PDF p.7, (16). C2: printed arbitrary pi is changed to a common
representation, because the proof chooses vectors in both fibers. For H=0 the
unit-trace state set is empty and the variational value is explicitly zero. 
Source correction disclosure (PLAN identifiers C2, C6):
Printed: C2: Lemma 4, PDF p.7, allows an arbitrary representation pi and writes a supremum over unit-trace positive operators, without a zero-H convention.
C6: The dilation formula on PDF p.2 calls pi a star homomorphism without explicitly requiring nondegeneracy.
Changed: C2: Require both dilation fibers nonempty; for the zero Hilbert space assign the trace variational quantity the explicit value zero.
C6: Use nondegenerate representations in dilation/GNS fibers (unital on a unital domain). The embedding sigma in Theorem 2 and Proposition 9 remains arbitrary.
Why: C2: An empty fiber gives beta_pi squared=4 but an empty overlap infimum; the proof chooses Vi in both fibers. At H=0 there are no trace-one states, while the dilation distance is zero.
C6: The source repeatedly uses V*V=T(1) and norm(V)^2=norm(T(1)) on PDF pp.2-3 and 7. Degenerate pi with an invisible component of V invalidates these identities; nondegeneracy implements the proof convention without normalizing V or restricting CP maps.
-/
theorem solution {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (H : CompleteComplexHilbert.{u}) {I : Type u} (b : HilbertBasis I ℂ H)
    (T1 T2 : A →L[ℂ] (H →L[ℂ] H)) (h1 : IsCStarCompletelyPositive T1) (h2 : IsCStarCompletelyPositive T2)
    (R : RepresentationData A)
    (hc : (dilationFiber H T1 R).Nonempty ∧ (dilationFiber H T2 R).Nonempty) :
    piDistance H T1 T2 R ^ 2 = traceVariational H b T1 T2 R := by
  unfold piDistance traceVariational
  rw [if_pos hc]
  set P := {r : ℝ | ∃ V1 ∈ dilationFiber H T1 R, ∃ V2 ∈ dilationFiber H T2 R, r = ‖V1 - V2‖} with hP
  obtain ⟨V1, hV1⟩ := hc.1
  obtain ⟨V2, hV2⟩ := hc.2
  have hPne : P.Nonempty := ⟨_, V1, hV1, V2, hV2, rfl⟩
  have hP0 : ∀ r ∈ P, 0 ≤ r := by
    rintro _ ⟨_, _, _, _, rfl⟩; exact norm_nonneg _
  by_cases hH : Subsingleton H
  · rw [if_pos hH]
    have hz : ∀ W1 W2 : H →L[ℂ] R.K, W1 - W2 = 0 := by
      intro W1 W2; ext x; rw [Subsingleton.elim x 0]; simp
    have : P = {0} := by
      ext r; constructor
      · rintro ⟨W1, _, W2, _, rfl⟩; simp [hz W1 W2]
      · rintro rfl; exact ⟨V1, hV1, V2, hV2, by simp [hz V1 V2]⟩
    rw [this, csInf_singleton]; ring
  · rw [if_neg hH]
    haveI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
    let g : ℝ → ℝ := fun x => (max x 0) ^ 2
    have hset : {r : ℝ | ∃ N ∈ overlapSet H T1 T2 R,
      r = sSup {q : ℝ | ∃ rho : QAlgorithms.Papers.Independent.Dependency50.P13.State b,
        q = (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp (T1 1))).re +
          (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp (T2 1))).re -
          2 * (QAlgorithms.Papers.Independent.Dependency50.P13.operatorTrace b
          (rho.val.val.comp N)).re}} = g '' P := by
      ext r; constructor
      · rintro ⟨N, ⟨W1, hW1, W2, hW2, rfl⟩, rfl⟩
        refine ⟨‖W1 - W2‖, ⟨W1, hW1, W2, hW2, rfl⟩, ?_⟩
        rw [g74i_T_one H T1 R W1 hW1, g74i_T_one H T2 R W2 hW2, g74i_KS]
        simp [g, max_eq_left (norm_nonneg _)]
      · rintro ⟨_, ⟨W1, hW1, W2, hW2, rfl⟩, rfl⟩
        refine ⟨W1.adjoint.comp W2, ⟨W1, hW1, W2, hW2, rfl⟩, ?_⟩
        rw [g74i_T_one H T1 R W1 hW1, g74i_T_one H T2 R W2 hW2, g74i_KS]
        simp [g, max_eq_left (norm_nonneg _)]
    rw [hset]
    have hmono : Monotone g := fun a c hac =>
      pow_le_pow_left₀ (le_max_right _ _) (max_le_max hac le_rfl) 2
    have hcont : ContinuousAt g (sInf P) :=
      ((continuous_id.max continuous_const).pow 2).continuousAt
    rw [← hmono.map_csInf_of_continuousAt hcont hPne ⟨0, hP0⟩]
    have : 0 ≤ sInf P := le_csInf hPne hP0
    simp [g, max_eq_left this]



end
