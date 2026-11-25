-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_R_exists_jacobian_minor_not_mem__658f34d01f6a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:38.79803+00:00
-- url     : https://prove2.me/submissions/e5aec1fd-f0e5-4008-b21c-2cfbbc0d1eb4

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
import Theorems.Thm_ReciprocityTheory_AnForm_R_gs_exists_rows_det_ne_zero
import Theorems.Thm_ReciprocityTheory_AnForm_R_gs_pderiv_facts
import Theorems.Thm_ReciprocityTheory_CA_exists_dim_trdeg_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {σ : Type} [Fintype σ]
    (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] {t : ℕ}
    (G : Fin t → MvPolynomial σ ℚ) (hG : Ideal.span (Set.range G) = 𝔭) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) = d) :
    ∃ (a : Fin (Fintype.card σ - d) → Fin t) (b : Fin (Fintype.card σ - d) → σ),
      Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∉ 𝔭 := by
  classical
  let A := MvPolynomial σ ℚ ⧸ 𝔭
  haveI : IsDomain A := Ideal.Quotient.isDomain 𝔭
  let K := FractionRing A
  let π : MvPolynomial σ ℚ →+* K := (algebraMap A K).comp (Ideal.Quotient.mk 𝔭)
  have hπ : ∀ f, π f = 0 ↔ f ∈ 𝔭 := by
    intro f
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff (R := A) (K := K), Ideal.Quotient.eq_zero_iff_mem]
  let xb : σ → A := fun s => Ideal.Quotient.mk 𝔭 (X s)
  have hmk : Ideal.Quotient.mkₐ ℚ 𝔭 = aeval xb := MvPolynomial.algHom_ext fun s => by
    rw [aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  have hmk' : ∀ f, Ideal.Quotient.mk 𝔭 f = aeval xb f := fun f => by
    rw [← hmk, Ideal.Quotient.mkₐ_eq_mk]

  haveI : Algebra.FiniteType ℚ A := inferInstance
  obtain ⟨s0, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℚ) (A := A)
  have hs0 : s0 = d := by
    have : (s0 : WithBot ℕ∞) = (d : WithBot ℕ∞) := hs1.symm.trans hd
    exact_mod_cast this
  subst hs0

  haveI : FaithfulSMul ℚ A :=
    (faithfulSMul_iff_algebraMap_injective ℚ A).mpr (algebraMap ℚ A).injective
  have hadj : Algebra.adjoin ℚ (Set.range xb) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, ← hmk]
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℚ 𝔭 x
    exact ⟨y, rfl⟩
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range xb)) A := by
    constructor
    intro a
    have ha : a ∈ Algebra.adjoin ℚ (Set.range xb) := by rw [hadj]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin ℚ (Set.range xb)) (A := A)
      (⟨a, ha⟩ : Algebra.adjoin ℚ (Set.range xb))
  obtain ⟨u, hu, hub⟩ := exists_isTranscendenceBasis_subset (R := ℚ) (Set.range xb)
  haveI : Finite u := ((Set.finite_range xb).subset hu).to_subtype
  haveI : Fintype u := Fintype.ofFinite u
  have hcardu : Fintype.card u = s0 := by
    have h1 := hub.cardinalMk_eq_trdeg
    rw [hs2, Cardinal.mk_fintype] at h1
    exact_mod_cast h1
  let g : u → σ := fun y => (hu y.2).choose
  have hg : ∀ y, xb (g y) = y := fun y => (hu y.2).choose_spec
  have hginj : Function.Injective g := by
    intro y y' h
    apply Subtype.ext
    rw [← hg y, ← hg y', h]

  have hind : ∀ Q : MvPolynomial σ ℚ, (↑Q.vars : Set σ) ⊆ Set.range g → Q ∈ 𝔭 → Q = 0 := by
    intro Q hQ hQp
    obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range Q g hginj hQ
    have h0 : aeval ((↑) : u → A) q = 0 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, hmk', aeval_rename] at hQp
      have hfun : ((↑) : u → A) = xb ∘ g := funext fun y => (hg y).symm
      rw [hfun]
      exact hQp
    rw [hub.1.eq_zero_of_aeval_eq_zero q h0, map_zero]

  have hrel : ∀ j, j ∉ Set.range g → ∃ Q : MvPolynomial σ ℚ,
      Q ∈ 𝔭 ∧ Q ≠ 0 ∧ (↑Q.vars : Set σ) ⊆ insert j (Set.range g) := by
    intro j hj
    let w : Option u → A := fun o => o.elim (xb j) ((↑) : u → A)
    have hw : ¬ AlgebraicIndependent ℚ w := by
      intro h
      rw [AlgebraicIndependent.option_iff] at h
      exact h.2 (hub.isAlgebraic.isAlgebraic (xb j))
    rw [algebraicIndependent_iff] at hw
    push_neg at hw
    obtain ⟨p, hp0, hp⟩ := hw
    let h : Option u → σ := fun o => o.elim j g
    have hinj : Function.Injective h := by
      rintro (_ | y) (_ | y') hyy
      · rfl
      · exact absurd ⟨y', hyy.symm⟩ hj
      · exact absurd ⟨y, hyy⟩ hj
      · exact congr_arg some (hginj hyy)
    refine ⟨rename h p, ?_, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, hmk', aeval_rename]
      have hfun : xb ∘ h = w := by
        funext o
        cases o with
        | none => rfl
        | some y => exact hg y
      rw [hfun]
      exact hp0
    · exact fun h0 => hp ((rename_injective h hinj) (h0.trans (map_zero _).symm))
    · intro i hi
      have := vars_rename h p (Finset.mem_coe.mp hi)
      obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp this
      cases o with
      | none => exact Set.mem_insert _ _
      | some y => exact Set.mem_insert_of_mem _ ⟨y, rfl⟩

  have hT : Fintype.card {j // j ∉ Set.range g} = Fintype.card σ - s0 := by
    rw [Fintype.card_subtype_compl, ← hcardu]
    congr 1
    rw [← Set.card_range_of_injective hginj]
  let e : {j // j ∉ Set.range g} ≃ Fin (Fintype.card σ - s0) := Fintype.equivFinOfCardEq hT
  let b : Fin (Fintype.card σ - s0) → σ := fun k => (e.symm k).1
  have hb : ∀ k, b k ∉ Set.range g := fun k => (e.symm k).2
  have hbinj : Function.Injective b := fun k k' h => e.symm.injective (Subtype.ext h)
  let M : Matrix (Fin t) (Fin (Fintype.card σ - s0)) K := Matrix.of fun i k => π (pderiv (b k) (G i))
  have hM : ∀ c, M.mulVec c = 0 → c = 0 := by
    intro c hc
    let D : MvPolynomial σ ℚ → K := fun f => ∑ k, π (pderiv (b k) f) * c k
    have hDG : ∀ i, D (G i) = 0 := fun i => by
      have := congr_fun hc i
      simpa [Matrix.mulVec, dotProduct, M, D] using this
    have hDp : ∀ f ∈ 𝔭, D f = 0 := by
      intro f hf
      rw [← hG] at hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hDG i
      | zero => simp [D]
      | add x y _ _ hx hy =>
        have : D (x + y) = D x + D y := by
          simp only [D, map_add, add_mul, Finset.sum_add_distrib]
        rw [this, hx, hy, add_zero]
      | smul a x hx' hx =>
        have hx0 : π x = 0 := (hπ x).2 (hG ▸ hx')
        have : D (a • x) = π a * D x := by
          simp only [D, smul_eq_mul, Derivation.leibniz, map_add, map_mul, hx0, zero_mul,
            add_zero, Finset.mul_sum, mul_assoc]
        rw [this, hx, mul_zero]
    funext k0
    let j := b k0
    have hj : j ∉ Set.range g := hb k0
    have hex : ∃ n, ∃ Q : MvPolynomial σ ℚ, Q ∈ 𝔭 ∧ Q ≠ 0 ∧
        (↑Q.vars : Set σ) ⊆ insert j (Set.range g) ∧ degreeOf j Q = n := by
      obtain ⟨Q, h1, h2, h3⟩ := hrel j hj
      exact ⟨_, Q, h1, h2, h3, rfl⟩
    obtain ⟨Q, hQp, hQ0, hQv, hQd⟩ := Nat.find_spec hex
    have hmin : ∀ Q' : MvPolynomial σ ℚ, Q' ∈ 𝔭 → Q' ≠ 0 →
        (↑Q'.vars : Set σ) ⊆ insert j (Set.range g) → degreeOf j Q ≤ degreeOf j Q' := by
      intro Q' h1 h2 h3
      rw [hQd]
      exact Nat.find_min' hex ⟨Q', h1, h2, h3, rfl⟩
    have hpos : 0 < degreeOf j Q := by
      by_contra h0
      push_neg at h0
      apply hQ0
      apply hind Q _ hQp
      intro i hi
      rcases hQv hi with rfl | hi'
      · exfalso
        rw [Finset.mem_coe, mem_vars] at hi
        obtain ⟨m, hm, him⟩ := hi
        have := monomial_le_degreeOf j hm
        rw [Finsupp.mem_support_iff] at him
        omega
      · exact hi'
    obtain ⟨hd0, hdlt, hdv⟩ := gs_pderiv_facts Q j hpos
    have hnot : π (pderiv j Q) ≠ 0 := by
      rw [Ne, hπ]
      intro hmem
      have := hmin _ hmem hd0 (fun i hi => hQv (Finset.mem_coe.mpr (hdv (Finset.mem_coe.mp hi))))
      omega
    have hDQ : D Q = π (pderiv j Q) * c k0 := by
      simp only [D]
      rw [Finset.sum_eq_single k0]
      · intro k _ hk
        have : pderiv (b k) Q = 0 := by
          apply pderiv_eq_zero_of_notMem_vars
          intro hv
          rcases hQv (Finset.mem_coe.mpr hv) with h | h
          · exact hk (hbinj h)
          · exact hb k h
        rw [this, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ k0) h
    have := hDp Q hQp
    rw [hDQ] at this
    simpa using (mul_eq_zero.mp this).resolve_left hnot
  obtain ⟨a, ha⟩ := gs_exists_rows_det_ne_zero M hM
  refine ⟨a, b, fun hmem => ha ?_⟩
  have h1 := (hπ _).2 hmem
  rw [RingHom.map_det] at h1
  have hM' : M.submatrix a id = π.mapMatrix (Matrix.of fun i j => pderiv (b j) (G (a i))) := by
    ext i k
    rfl
  rw [hM']
  exact h1
end ReciprocityTheory.AnForm.R
