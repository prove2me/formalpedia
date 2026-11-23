-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Yzb5.relIndex_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:22.731297+00:00
-- url     : https://prove2.me/submissions/b0140970-a344-4931-9911-c108fb1f397e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardQuotPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private lemma UpperTheory.Reformulated.B.Yzb5.card_quot_pow {R : Type*} [CommRing R] [IsDomain R] (p : R) (hp : p ≠ 0)
    (n : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ n}) = Nat.card (R ⧸ Ideal.span {p}) ^ n := by
  have hidx : ∀ x : R, Nat.card (R ⧸ Ideal.span {x}) = (Ideal.span {x}).toAddSubgroup.index :=
    fun x => rfl
  induction n with
  | zero =>
    have : (Ideal.span {(1 : R)}) = ⊤ := Ideal.span_singleton_one
    simp [this]
  | succ n ih =>
    have hinj : Function.Injective (AddMonoidHom.mulLeft (p ^ n)) :=
      mul_right_injective₀ (pow_ne_zero n hp)
    have h1 : AddSubgroup.map (AddMonoidHom.mulLeft (p ^ n)) (Ideal.span {p}).toAddSubgroup
        = (Ideal.span {p ^ (n + 1)}).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton,
        AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
        exact ⟨c, by ring⟩
      · rintro ⟨c, rfl⟩
        exact ⟨p * c, ⟨c, rfl⟩, by ring⟩
    have h2 : AddSubgroup.map (AddMonoidHom.mulLeft (p ^ n)) (⊤ : AddSubgroup R)
        = (Ideal.span {p ^ n}).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton,
        AddMonoidHom.coe_mulLeft, AddSubgroup.mem_top, true_and]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨c, rfl⟩
    have h3 : (Ideal.span {p ^ (n + 1)}).toAddSubgroup.relIndex (Ideal.span {p ^ n}).toAddSubgroup
        = (Ideal.span {p}).toAddSubgroup.index := by
      rw [← h1, ← h2, AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
        AddSubgroup.relIndex_top_right]
    have hle : (Ideal.span {p ^ (n + 1)}).toAddSubgroup ≤ (Ideal.span {p ^ n}).toAddSubgroup := by
      rw [← h1, ← h2]
      exact AddSubgroup.map_mono le_top
    rw [hidx, ← AddSubgroup.relIndex_top_right,
      ← AddSubgroup.relIndex_mul_relIndex _ _ _ hle le_top, h3,
      AddSubgroup.relIndex_top_right, ← hidx p, ← hidx (p ^ n), ih, pow_succ, mul_comm]
private lemma UpperTheory.Reformulated.B.Yzb5.card_coker {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {p : R} (hp : Irreducible p) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (hM : M.det ≠ 0) :
    ∃ (m : ℕ) (v : Rˣ), M.det = (v : R) * p ^ m ∧
      Nat.card ((ι → R) ⧸ LinearMap.range M.mulVecLin) = Nat.card (R ⧸ Ideal.span {p}) ^ m := by
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hM hx
  have hrank : Module.finrank R (LinearMap.range M.mulVecLin) = Module.finrank R (ι → R) :=
    LinearMap.finrank_range_of_inj hinj
  let b0 := Pi.basisFun R ι
  let b' := Submodule.smithNormalFormTopBasis b0 hrank
  let a := Submodule.smithNormalFormCoeffs b0 hrank
  let ab := Submodule.smithNormalFormBotBasis b0 hrank
  have hab : ∀ i, (ab i : ι → R) = a i • b' i := Submodule.smithNormalFormBotBasis_def b0 hrank
  have ha0 : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b0 hrank
  let e := LinearEquiv.ofInjective M.mulVecLin hinj
  let c : Module.Basis ι R (ι → R) := ab.map e.symm
  have hc : ∀ i, M.mulVecLin (c i) = a i • b' i := by
    intro i
    rw [← hab i]
    have h := LinearEquiv.ofInjective_apply (f := M.mulVecLin) (h := hinj) (c i)
    rw [← h]
    simp [c, e]
  have hdet : b'.det (M.mulVecLin ∘ c) = ∏ i, a i := by
    rw [Module.Basis.det_apply]
    have : b'.toMatrix (M.mulVecLin ∘ c) = Matrix.diagonal a := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hc, Matrix.diagonal_apply, Finsupp.single_apply, eq_comm]
      split_ifs with h
      · rw [h]
      · rfl
    rw [this, Matrix.det_diagonal]
  have hcomp := b'.det_comp M.mulVecLin c
  rw [hdet, ← Matrix.toLin'_apply', LinearMap.det_toLin'] at hcomp
  choose k hk using fun i => IsDiscreteValuationRing.associated_pow_irreducible (ha0 i) hp
  have hprod : Associated (∏ i, a i) (p ^ ∑ i, k i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Associated.prod _ _ _ (fun i _ => hk i)
  obtain ⟨w, hw⟩ := b'.isUnit_det c
  have hassoc : Associated M.det (p ^ ∑ i, k i) :=
    Associated.trans ⟨w, by rw [hw, hcomp]⟩ hprod
  obtain ⟨v, hv⟩ := hassoc.symm
  refine ⟨∑ i, k i, v, by rw [← hv, mul_comm], ?_⟩
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan _ b0 hrank).toEquiv, Nat.card_pi,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hs : Ideal.span {Submodule.smithNormalFormCoeffs b0 hrank i} = Ideal.span {p ^ k i} :=
    Ideal.span_singleton_eq_span_singleton.mpr (hk i)
  rw [hs, UpperTheory.Reformulated.B.Yzb5.card_quot_pow p hp.ne_zero]
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yzb5
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F]
      {ϖ : ↥(ValuativeRel.valuation F).integer},
      Irreducible ϖ →
        ∀ {W : Type} [inst_4 : AddCommGroup W] [inst_5 : _root_.Module F W] {ι : Type} [Fintype ι] (b : Module.Basis ι F W)
          (ψ : W →ₗ[F] W) (a : ℤ) (u : (↥(ValuativeRel.valuation F).integer)ˣ),
          (LinearMap.det : (W →ₗ[F] W) → F) ψ = (↑ϖ : F) ^ a * (↑(↑u : ↥(ValuativeRel.valuation F).integer) : F) →
            ∀ (W0 : AddSubgroup W),
              (∀ (x : W), x ∈ W0 ↔ ∀ (i : ι), ((b.repr : W → ι →₀ F) x : ι → F) i ∈ (ValuativeRel.valuation F).integer) →
                (∀ (i j : ι),
                    ((b.repr : W → ι →₀ F) ((ψ : W → W) ((b : ι → W) j)) : ι → F) i ∈ (ValuativeRel.valuation F).integer) →
                  ∃ (m : ℕ), a = (↑m : ℤ) ∧ (AddSubgroup.map ψ.toAddMonoidHom W0).relIndex W0 = UpperTheory.Reformulated.B.Yzb5.resQ ϖ ^ m := by
  intro F _ _ _ _ ϖ hϖ W _ _ ι _ b ψ a u hdet W0 hW0 hint
  classical
  let f := (ValuativeRel.valuation F).integer.subtype
  let M : Matrix ι ι (ValuativeRel.valuation F).integer := fun i j => ⟨b.repr (ψ (b j)) i, hint i j⟩
  have hMdet : f M.det = LinearMap.det ψ := by
    rw [RingHom.map_det, ← LinearMap.det_toMatrix b ψ]
    congr 1
    ext i j
    simp [f, M, LinearMap.toMatrix_apply]
    rfl
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu0 : ((u : (ValuativeRel.valuation F).integer) : F) ≠ 0 :=
    fun h => u.ne_zero (Subtype.ext h)
  have hM0 : M.det ≠ 0 := by
    intro h
    rw [h, map_zero, hdet] at hMdet
    exact mul_ne_zero (zpow_ne_zero a hϖ0) hu0 hMdet.symm
  obtain ⟨m, v, hv, hcard⟩ := UpperTheory.Reformulated.B.Yzb5.card_coker hϖ M hM0
  have hint' := Valuation.integer.integers (ValuativeRel.valuation F)
  have hlt : ValuativeRel.valuation F (ϖ : F) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hϖ.not_isUnit
  have hpos : 0 < ValuativeRel.valuation F (ϖ : F) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hϖ0
  have ham : a = (m : ℤ) := by
    have h1 : (ϖ : F) ^ a * ((u : (ValuativeRel.valuation F).integer) : F)
        = ((v : (ValuativeRel.valuation F).integer) : F) * (ϖ : F) ^ (m : ℤ) := by
      rw [← hdet, ← hMdet, hv]
      simp [f]
    have h2 := congrArg (ValuativeRel.valuation F) h1
    have hu1 : ValuativeRel.valuation F ((u : (ValuativeRel.valuation F).integer) : F) = 1 :=
      hint'.isUnit_iff_valuation_eq_one.mp u.isUnit
    have hv1 : ValuativeRel.valuation F ((v : (ValuativeRel.valuation F).integer) : F) = 1 :=
      hint'.isUnit_iff_valuation_eq_one.mp v.isUnit
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀, hu1, hv1, mul_one, one_mul] at h2
    exact (zpow_right_strictAnti₀ hpos hlt).injective h2
  refine ⟨m, ham, ?_⟩
  let e : (ι → (ValuativeRel.valuation F).integer) →+ W :=
    (b.equivFun.symm.toLinearMap.toAddMonoidHom).comp (AddMonoidHom.compLeft f.toAddMonoidHom ι)
  have he : ∀ x i, b.repr (e x) i = (x i : F) := by
    intro x i
    have h : b.equivFun (e x) i = (x i : F) := by
      change b.equivFun (b.equivFun.symm fun i => (x i : F)) i = _
      rw [LinearEquiv.apply_symm_apply]
    exact h
  have hinj : Function.Injective e := by
    intro x y hxy
    ext i
    rw [← he x i, ← he y i, hxy]
  have hrange : AddSubgroup.map e ⊤ = W0 := by
    ext w
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, hW0]
    constructor
    · rintro ⟨x, rfl⟩ i
      rw [he]
      exact (x i).2
    · intro h
      refine ⟨fun i => ⟨b.repr w i, h i⟩, ?_⟩
      apply b.repr.injective
      ext i
      rw [he]
  have hcomm : ∀ x, e (M.mulVecLin x) = ψ (e x) := by
    intro x
    apply b.repr.injective
    ext i
    rw [he]
    have hx := b.sum_repr (e x)
    simp only [he] at hx
    have hmv : ((M.mulVecLin x) i : F) = f (∑ j, M i j * x j) := rfl
    rw [hmv, map_sum, ← hx, map_sum, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    rfl
  have hmap : AddSubgroup.map ψ.toAddMonoidHom W0
      = AddSubgroup.map e (LinearMap.range M.mulVecLin).toAddSubgroup := by
    ext w
    rw [← hrange]
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, Submodule.mem_toAddSubgroup,
      LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, hcomm x⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, (hcomm x).symm⟩
  rw [hmap, ← hrange, AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
    AddSubgroup.relIndex_top_right]
  exact hcard
end UpperTheory.Reformulated.B.Yzb5
