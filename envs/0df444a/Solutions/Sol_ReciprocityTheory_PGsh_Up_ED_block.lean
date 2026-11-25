-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.ED.block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:46:30.507077+00:00
-- url     : https://prove2.me/submissions/10ae2296-9974-4a69-b3af-8a5d20ba1a84

import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsSmulMemOfMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_DotSingle
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_dot_single
import Theorems.Thm_ReciprocityTheory_PGsh_Up_ED_eq_of_dot
import Theorems.Thm_ReciprocityTheory_PGsh_L2_SecondCohomologyLattice_free_of_finite_torsionFree
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_hasLen_coker_det
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_smith_mat
import Theorems.Thm_ReciprocityTheory_PGsh_Up_hasLen_unique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.ED
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.ED
theorem _root_.solution (hv : v.Integers R) {ι κ' : Type} [Fintype ι] [DecidableEq ι] [Fintype κ']
    [DecidableEq κ'] (Φ : Matrix κ' ι R)
    (ε : Matrix ι ι R) (hε : ε * ε = ε) (Pq : Matrix κ' κ' R) (Qs : Submodule R (κ' → R))
    (hPqmem : ∀ w, Pq *ᵥ w ∈ Qs) (hPqid : ∀ w ∈ Qs, Pq *ᵥ w = w) (hcomm : Φ * ε = Pq * Φ)
    (n : ℕ) (hnT : Module.finrank R (LinearMap.range (Matrix.mulVecLin ε)) = n)
    (hnQ : Module.finrank R Qs = n) (X : NNReal)
    (hX : HasLen v R (Qs ⧸ ((LinearMap.range (Matrix.mulVecLin ε)).map (Matrix.mulVecLin Φ)).comap
      Qs.subtype) X)
    (cp : R) (hcp : ∀ w : ι → R, w ᵥ* ε = w → ∃ u : κ' → R, cp • w = u ᵥ* (Φ * ε)) :
    ∃ (lam : Fin n → ι → R) (a : Fin n → R) (y : Fin n → ι → R),
      (∀ j, lam j ᵥ* ε = lam j) ∧ (∀ l, ε *ᵥ y l = y l) ∧
      (∀ j l, lam j ⬝ᵥ y l = if j = l then 1 else 0) ∧ (∀ j, ∃ c, cp = a j * c) ∧
      ∏ j, v (algebraMap R C (a j)) = X ∧
      Submodule.span R (Set.range fun k => (Φ * ε) k) =
        Submodule.span R (Set.range fun j => a j • lam j) := by
  classical
  have : IsDomain R := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  set T := LinearMap.range (Matrix.mulVecLin ε) with hT
  have hQeq : Qs = LinearMap.range (Matrix.mulVecLin Pq) :=
    le_antisymm (fun w hw => ⟨w, hPqid w hw⟩) (by rintro _ ⟨w, rfl⟩; exact hPqmem w)
  have hTfg : T.FG := by rw [hT, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have hQfg : Qs.FG := by rw [hQeq, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have htf : ∀ {α : Type} (S : Submodule R (α → R)) (r : R) (x : S), r ≠ 0 → r • x = 0 → x = 0 := by
    rintro α S r ⟨x, hx⟩ hr h
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val h) i
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero,
      Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hr
  have : Module.Finite R T := Module.Finite.iff_fg.2 hTfg
  have : Module.Finite R Qs := Module.Finite.iff_fg.2 hQfg
  have : Module.Free R T := L2.SecondCohomologyLattice.free_of_finite_torsionFree T (htf T)
  have : Module.Free R Qs := L2.SecondCohomologyLattice.free_of_finite_torsionFree Qs (htf Qs)
  set β := Module.finBasisOfFinrankEq R T hnT with hβ
  set γ := Module.finBasisOfFinrankEq R Qs hnQ with hγ
  have hεT : ∀ t ∈ T, ε *ᵥ t = t := by
    rintro _ ⟨x, rfl⟩
    show ε *ᵥ (ε *ᵥ x) = ε *ᵥ x
    rw [mulVec_mulVec, hε]
  have hΦT : ∀ t : T, Φ *ᵥ (t : ι → R) ∈ Qs := by
    rintro ⟨_, x, rfl⟩
    show Φ *ᵥ (ε *ᵥ x) ∈ Qs
    rw [mulVec_mulVec, hcomm, ← mulVec_mulVec]
    exact hPqmem _
  set Φi : T →ₗ[R] Qs :=
    LinearMap.codRestrict Qs ((Matrix.mulVecLin Φ).comp T.subtype) hΦT with hΦi
  have hΦiapp : ∀ t : T, ((Φi t : Qs) : κ' → R) = Φ *ᵥ (t : ι → R) := fun _ => rfl
  set M := LinearMap.toMatrix β γ Φi with hM

  have hrange : ((T.map (Matrix.mulVecLin Φ)).comap Qs.subtype) = LinearMap.range Φi := by
    ext q
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨t, ht, htq⟩
      exact ⟨⟨t, ht⟩, Subtype.ext htq⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, rfl⟩
  have hkey : ∀ t : T, γ.equivFun (Φi t) = M *ᵥ β.equivFun t := by
    intro t
    simp only [Module.Basis.equivFun_apply]
    rw [hM, LinearMap.toMatrix_mulVec_repr]
  have hmapM : (LinearMap.range Φi).map γ.equivFun.toLinearMap =
      LinearMap.range (Matrix.mulVecLin M) := by
    ext z
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨β.equivFun t, (hkey t).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨Φi (β.equivFun.symm c), ⟨_, rfl⟩, ?_⟩
      show γ.equivFun (Φi (β.equivFun.symm c)) = M *ᵥ c
      rw [hkey, LinearEquiv.apply_symm_apply]
  have hLen : HasLen v R (Qs ⧸ ((T.map (Matrix.mulVecLin Φ)).comap Qs.subtype))
      (v (algebraMap R C M.det)) := by
    obtain ⟨m', c', ⟨f⟩, hf⟩ := Smith.hasLen_coker_det (C := C) (v := v) hv M
    exact ⟨m', c', ⟨((Submodule.quotEquivOfEq _ _ hrange).trans
      (Submodule.Quotient.equiv _ _ γ.equivFun hmapM)).trans f⟩, hf⟩
  have hXM : X = v (algebraMap R C M.det) := hasLen_unique hv hX hLen

  obtain ⟨P, Q', a, hP, hQ', hD⟩ := Smith.smith_mat hv n n Mᵀ
  have hdiag : P * Mᵀ * Q' = Matrix.diagonal a := by
    ext j k
    rw [hD, Matrix.diagonal_apply]
    by_cases h : j = k
    · subst h; simp
    · have : (k : ℕ) ≠ (j : ℕ) := fun e => h (Fin.ext e.symm)
      simp [h, this]
  have hprod : ∏ j, v (algebraMap R C (a j)) = X := by
    rw [hXM, ← map_prod, ← map_prod, ← Matrix.det_diagonal, ← hdiag, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose, map_mul, map_mul, map_mul, map_mul,
      hv.one_of_isUnit hP, hv.one_of_isUnit hQ', one_mul, mul_one]
  set Pi' := P⁻¹ with hPi'
  have hPP : P * Pi' = 1 := Matrix.mul_nonsing_inv P hP
  have hPP' : Pi' * P = 1 := Matrix.nonsing_inv_mul P hP

  set ℓ : Fin n → (ι → R) →ₗ[R] R :=
    fun l => (β.coord l).comp (Matrix.mulVecLin ε).rangeRestrict with hℓ
  have hℓε : ∀ l x, ℓ l (ε *ᵥ x) = ℓ l x := by
    intro l x
    simp only [hℓ, LinearMap.coe_comp, Function.comp_apply]
    congr 1
    apply Subtype.ext
    show ε *ᵥ (ε *ᵥ x) = ε *ᵥ x
    rw [mulVec_mulVec, hε]
  have hℓβ : ∀ l m, ℓ l (β m : ι → R) = if m = l then 1 else 0 := by
    intro l m
    simp only [hℓ, LinearMap.coe_comp, Function.comp_apply]
    have : (Matrix.mulVecLin ε).rangeRestrict (β m : ι → R) = β m := by
      apply Subtype.ext
      show ε *ᵥ (β m : ι → R) = β m
      exact hεT _ (β m).2
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  set lam : Fin n → ι → R := fun j k => ∑ l, Pi' l j * ℓ l (Pi.single k 1) with hlam
  have hlamdot : ∀ j x, lam j ⬝ᵥ x = ∑ l, Pi' l j * ℓ l x := by
    intro j x
    have e : lam j = fun k => (∑ l, Pi' l j • ℓ l) (Pi.single k 1) := by
      funext k; simp [hlam, LinearMap.sum_apply]
    rw [e, dot_single]
    simp [LinearMap.sum_apply]
  set y : Fin n → ι → R := fun l => ∑ m, P l m • (β m : ι → R) with hy
  have hyT : ∀ l, y l ∈ T := fun l =>
    Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (β m).2

  have hdotε : ∀ (w : ι → R) x, (w ᵥ* ε) ⬝ᵥ x = w ⬝ᵥ (ε *ᵥ x) := fun w x =>
    (Matrix.dotProduct_mulVec w ε x).symm
  have hlamε : ∀ j, lam j ᵥ* ε = lam j := by
    intro j
    apply eq_of_dot
    intro x
    rw [hdotε, hlamdot, hlamdot]
    simp only [hℓε]
  have hlamy : ∀ j l, lam j ⬝ᵥ y l = if j = l then 1 else 0 := by
    intro j l
    rw [hlamdot]
    have e1 : ∀ l', ℓ l' (y l) = P l l' := by
      intro l'
      simp only [hy, map_sum, map_smul, hℓβ, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [e1]
    have := congrFun (congrFun hPP l) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    have h2 : (if j = l then (1 : R) else 0) = if l = j then 1 else 0 := by
      by_cases h : j = l <;> simp [h, eq_comm]
    rw [h2, ← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

  let K : (ι → R) →ₗ[R] (Fin n → R) :=
    { toFun := fun w l => w ⬝ᵥ (β l : ι → R)
      map_add' := fun w w' => by funext l; simp [add_dotProduct]
      map_smul' := fun c w => by funext l; simp [smul_dotProduct] }
  have hKapp : ∀ w l, K w l = w ⬝ᵥ (β l : ι → R) := fun _ _ => rfl
  have hKlam : ∀ j, K (lam j) = fun l => Pi' l j := by
    intro j; funext l
    rw [hKapp, hlamdot]
    simp only [hℓβ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  set cvec : κ' → Fin n → R := fun k m => (γ m : κ' → R) k with hcvec
  have hKrow : ∀ k, K ((Φ * ε) k) = Mᵀ *ᵥ cvec k := by
    intro k; funext l
    rw [hKapp]
    have e1 : (Φ * ε) k ⬝ᵥ (β l : ι → R) = ((Φ * ε) *ᵥ (β l : ι → R)) k := rfl
    rw [e1, ← mulVec_mulVec, hεT _ (β l).2, ← hΦiapp]
    have e2 : ((Φi (β l) : Qs) : κ' → R) = ∑ m, M m l • (γ m : κ' → R) := by
      have h := γ.sum_repr (Φi (β l))
      rw [← h]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hM, LinearMap.toMatrix_apply]
    rw [e2, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, transpose_apply, hcvec]

  set gs : Fin n → κ' → R := fun m k => γ.coord m ⟨Pq *ᵥ Pi.single k 1, hPqmem _⟩ with hgs
  have hgsc : ∀ m m', ∑ k, gs m k * cvec k m' = if m' = m then 1 else 0 := by
    intro m m'
    let f : (κ' → R) →ₗ[R] R := (γ.coord m).comp
      (LinearMap.codRestrict Qs (Matrix.mulVecLin Pq) hPqmem)
    have hf : ∀ k, f (Pi.single k 1) = gs m k := fun k => rfl
    have h1 : (fun k => f (Pi.single k 1)) ⬝ᵥ (γ m' : κ' → R) = f (γ m') := dot_single f _
    have h2 : f (γ m') = if m' = m then 1 else 0 := by
      have : LinearMap.codRestrict Qs (Matrix.mulVecLin Pq) hPqmem (γ m' : κ' → R) = γ m' :=
        Subtype.ext (hPqid _ (γ m').2)
      simp only [f, LinearMap.coe_comp, Function.comp_apply, this, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_apply]
    rw [← h2, ← h1]
    simp only [dotProduct, hf, hcvec]

  have hMrange : ∀ z, Mᵀ *ᵥ z ∈ Submodule.span R (Set.range fun k => Mᵀ *ᵥ cvec k) := by
    intro z
    have hz : z = ∑ k, (∑ m, z m * gs m k) • cvec k := by
      funext m'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum, hgsc, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hz, mulVec_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [mulVec_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hmapN : (Submodule.span R (Set.range fun k => (Φ * ε) k)).map K =
      LinearMap.range (Matrix.mulVecLin Mᵀ) := by
    rw [Submodule.map_span, ← Set.range_comp]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨cvec k, (hKrow k).symm⟩
    · rintro _ ⟨z, rfl⟩
      have e : (K ∘ fun k => (Φ * ε) k) = fun k => Mᵀ *ᵥ cvec k := funext hKrow
      rw [e]
      exact hMrange z
  have hmapS : (Submodule.span R (Set.range fun j => a j • lam j)).map K =
      LinearMap.range (Matrix.mulVecLin Mᵀ) := by
    rw [Submodule.map_span, ← Set.range_comp]
    have e1 : (K ∘ fun j => a j • lam j) = fun j => fun l => (Pi' * Matrix.diagonal a) l j := by
      funext j l
      simp only [Function.comp_apply, map_smul, hKlam, Pi.smul_apply, smul_eq_mul,
        Matrix.mul_diagonal]
      ring
    rw [e1]
    have e2 : Pi' * Matrix.diagonal a = Mᵀ * Q' := by
      rw [← hdiag, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
    rw [e2]
    have e3 : Submodule.span R (Set.range fun j => fun l => (Mᵀ * Q') l j) =
        LinearMap.range (Matrix.mulVecLin (Mᵀ * Q')) := by
      rw [Matrix.range_mulVecLin]; rfl
    rw [e3]
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩; exact ⟨Q' *ᵥ z, by simp [mulVec_mulVec]⟩
    · rintro _ ⟨z, rfl⟩
      refine ⟨Q'⁻¹ *ᵥ z, ?_⟩
      show (Mᵀ * Q') *ᵥ (Q'⁻¹ *ᵥ z) = Mᵀ *ᵥ z
      rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ', Matrix.mul_one]

  have hKinj : ∀ w w', w ᵥ* ε = w → w' ᵥ* ε = w' → K w = K w' → w = w' := by
    intro w w' hw hw' hK
    have hT0 : ∀ t ∈ T, w ⬝ᵥ t = w' ⬝ᵥ t := by
      intro t ht
      have : t = ∑ l, β.repr ⟨t, ht⟩ l • (β l : ι → R) := by
        have h := congrArg Subtype.val (β.sum_repr ⟨t, ht⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h
        exact h.symm
      rw [this, dotProduct_sum, dotProduct_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dotProduct_smul, dotProduct_smul]
      have := congrFun hK l
      rw [hKapp, hKapp] at this
      rw [this]
    apply eq_of_dot
    intro x
    rw [← hw, ← hw', hdotε, hdotε]
    exact hT0 _ ⟨x, rfl⟩
  have hrowε : ∀ k, (Φ * ε) k ᵥ* ε = (Φ * ε) k := by
    intro k
    funext k'
    simp only [vecMul, dotProduct]
    have := congrFun (congrFun (show Φ * ε * ε = Φ * ε by rw [Matrix.mul_assoc, hε]) k) k'
    rw [Matrix.mul_apply] at this
    exact this
  have hNle : ∀ w ∈ Submodule.span R (Set.range fun k => (Φ * ε) k), w ᵥ* ε = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨k, rfl⟩ := hw; exact hrowε k
    | zero => simp
    | add x y _ _ hx hy => rw [add_vecMul, hx, hy]
    | smul c x _ hx => rw [smul_vecMul, hx]
  have hSle : ∀ w ∈ Submodule.span R (Set.range fun j => a j • lam j), w ᵥ* ε = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨j, rfl⟩ := hw; rw [smul_vecMul, hlamε]
    | zero => simp
    | add x y _ _ hx hy => rw [add_vecMul, hx, hy]
    | smul c x _ hx => rw [smul_vecMul, hx]
  have hspan : Submodule.span R (Set.range fun k => (Φ * ε) k) =
      Submodule.span R (Set.range fun j => a j • lam j) := by
    apply le_antisymm
    · intro w hw
      have hKw : K w ∈ (Submodule.span R (Set.range fun j => a j • lam j)).map K := by
        rw [hmapS, ← hmapN]; exact ⟨w, hw, rfl⟩
      obtain ⟨s, hs, hsw⟩ := hKw
      rw [← hKinj s w (hSle s hs) (hNle w hw) hsw]
      exact hs
    · intro w hw
      have hKw : K w ∈ (Submodule.span R (Set.range fun k => (Φ * ε) k)).map K := by
        rw [hmapN, ← hmapS]; exact ⟨w, hw, rfl⟩
      obtain ⟨s, hs, hsw⟩ := hKw
      rw [← hKinj s w (hNle s hs) (hSle w hw) hsw]
      exact hs

  have hdvd : ∀ j, ∃ c, cp = a j * c := by
    intro j
    obtain ⟨u, hu⟩ := hcp (lam j) (hlamε j)
    have hmem : cp • lam j ∈ Submodule.span R (Set.range fun k => (Φ * ε) k) := by
      rw [hu]
      have e : u ᵥ* (Φ * ε) = ∑ k, u k • (Φ * ε) k := by
        funext k'; simp [vecMul, dotProduct, Finset.sum_apply]
      rw [e]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have hK := Submodule.mem_map_of_mem (f := K) hmem
    rw [hmapN] at hK
    obtain ⟨z, hz⟩ := hK

    have hz' : Mᵀ *ᵥ z = cp • fun l => Pi' l j := by
      rw [← hKlam, ← map_smul]; exact hz
    have h2 : Matrix.diagonal a *ᵥ (Q'⁻¹ *ᵥ z) = cp • Pi.single j 1 := by
      rw [← hdiag, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hQ',
        Matrix.mul_one, ← mulVec_mulVec]
      show P *ᵥ (Mᵀ *ᵥ z) = _
      rw [hz']
      funext l
      simp only [mulVec_smul, Pi.smul_apply, smul_eq_mul]
      have := congrFun (congrFun hPP l) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simp only [mulVec, dotProduct, this, Pi.single_apply, eq_comm]
    have h3 := congrFun h2 j
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one] at h3
    exact ⟨_, h3.symm⟩
  refine ⟨lam, a, y, hlamε, fun l => hεT _ (hyT l), hlamy, hdvd, hprod, hspan⟩
end ReciprocityTheory.PGsh.Up.ED
