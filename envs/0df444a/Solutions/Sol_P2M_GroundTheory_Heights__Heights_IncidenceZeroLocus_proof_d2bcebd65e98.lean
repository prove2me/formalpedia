-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_proof_d2bcebd65e98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:30:57.986093+00:00
-- url     : https://prove2.me/submissions/acf41b32-1f7e-485a-ad48-115d2f3cee15

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_exists_det_submatrix_ne_zero_613386e27c04
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_homogeneousComponent_map_a897c7422d0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_mem_finsuppAntidiag_univ_iff_5c8a1f46e0c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_eval__eq_sum_degree_5c698ff6417a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceZeroLocus
namespace GroundTheory.Heights₂.Heights.IncidenceZeroLocus
theorem _root_.solution : IncidenceZeroLocus.Statement := by
  classical
  intro F _ n k Q hQ Ω _ _ _ v hv
  by_contra hno
  push Not at hno
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian Q : Q.FG)
  have hSQ : ∀ q ∈ S, q ∈ Q := fun q hq => by rw [← hS]; exact Submodule.subset_span hq
  let G : (S ⊕ Fin k) → MvPolynomial (Fin n) (MvPolynomial (Fin k × Fin n) F) :=
    Sum.elim (fun q => map (algebraMap F (MvPolynomial (Fin k × Fin n) F)) (q : MvPolynomial (Fin n) F))
      (fun i => ∑ j, C (X (i, j)) * X j)
  let φv : MvPolynomial (Fin k × Fin n) F →+* Ω := (aeval v : MvPolynomial (Fin k × Fin n) F →ₐ[F] Ω)
  have hφv : φv.comp (algebraMap F (MvPolynomial (Fin k × Fin n) F)) = algebraMap F Ω :=
    AlgHom.comp_algebraMap _
  let Jv : Ideal (MvPolynomial (Fin n) Ω) := Ideal.span (Set.range fun t => map φv (G t))

  have hzero : ∀ y ∈ zeroLocus Ω Jv, y = 0 := by
    intro y hy
    by_contra hy0
    have hyQ : ∀ q ∈ Q, aeval y q = 0 := by
      have hle : Q ≤ RingHom.ker (aeval y : MvPolynomial (Fin n) F →ₐ[F] Ω) := by
        rw [← hS, Submodule.span_le]
        intro q hq
        have h := hy _ (Ideal.subset_span ⟨Sum.inl ⟨q, hq⟩, rfl⟩)
        simp only [G, Sum.elim_inl, map_map, hφv] at h
        rw [SetLike.mem_coe, RingHom.mem_ker, ← h, aeval_def, aeval_def, eval₂_map]
        simp
      exact fun q hq => hle hq
    obtain ⟨i, hi⟩ := hno y hy0 hyQ
    have h := hy _ (Ideal.subset_span ⟨Sum.inr i, rfl⟩)
    simp [G, φv, coe_aeval_eq_eval] at h
    exact hi h
  have hrad : ∀ j, ∃ m, (X j : MvPolynomial (Fin n) Ω) ^ m ∈ Jv := by
    intro j
    have h : (X j : MvPolynomial (Fin n) Ω) ∈ vanishingIdeal Ω (zeroLocus Ω Jv) := by
      rw [mem_vanishingIdeal_iff]
      intro y hy
      rw [hzero y hy]
      simp
    rw [vanishingIdeal_zeroLocus_eq_radical] at h
    exact h
  choose e he using hrad
  set N := ∑ j, e j + 1 with hN

  have hmono : ∀ f : Fin n →₀ ℕ, f.degree = N → monomial f (1 : Ω) ∈ Jv := by
    intro f hf
    obtain ⟨j, hj⟩ : ∃ j, e j ≤ f j := by
      by_contra h
      push Not at h
      have hle : ∑ j, f j ≤ ∑ j, e j := Finset.sum_le_sum fun j _ => (h j).le
      rw [← Finsupp.degree_eq_sum, hf] at hle
      omega
    have hle : Finsupp.single j (e j) ≤ f := Finsupp.single_le_iff.mpr hj
    have h : monomial f (1 : Ω) = X j ^ e j * monomial (f - Finsupp.single j (e j)) 1 := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul, add_tsub_cancel_of_le hle]
    rw [h]
    exact Jv.mul_mem_right _ (he j)
  let Rows : Finset (Fin n →₀ ℕ) := (Finset.univ : Finset (Fin n)).finsuppAntidiag N
  let Mf : Finset (Fin n →₀ ℕ) :=
    (Finset.range (N + 1)).biUnion fun d => (Finset.univ : Finset (Fin n)).finsuppAntidiag d
  have memMf : ∀ m, m ∈ Mf ↔ m.degree ≤ N := fun m => by
    simp [Mf, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum, Nat.lt_succ_iff]
  let c : (S ⊕ Fin k) × Mf → MvPolynomial (Fin n) (MvPolynomial (Fin k × Fin n) F) :=
    fun p => homogeneousComponent N (monomial (p.2 : Fin n →₀ ℕ) 1 * G p.1)
  let Mx : Matrix Rows ((S ⊕ Fin k) × Mf) (MvPolynomial (Fin k × Fin n) F) :=
    fun f p => coeff (f : Fin n →₀ ℕ) (c p)

  have hspanv : ∀ f : Rows, Pi.single f 1 ∈ Submodule.span Ω (Set.range (Mx.map φv).col) := by
    let π : MvPolynomial (Fin n) Ω →ₗ[Ω] (Rows → Ω) :=
      LinearMap.pi fun f => lcoeff Ω (f : Fin n →₀ ℕ)
    let W := Submodule.span Ω (Set.range fun p => map φv (c p))
    have hWle : W.map π ≤ Submodule.span Ω (Set.range (Mx.map φv).col) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨p, ?_⟩
      ext f
      simp [π, Mx, coeff_map, Matrix.col]
      rfl
    have hterm : ∀ t (m : Fin n →₀ ℕ),
        homogeneousComponent N (monomial m (1 : Ω) * map φv (G t)) ∈ W := by
      intro t m
      by_cases hm : m ∈ Mf
      · refine Submodule.subset_span ⟨(t, ⟨m, hm⟩), ?_⟩
        simp only [c]
        rw [← homogeneousComponent_map, map_mul, map_monomial, map_one φv]
      · rw [homogeneousComponent_eq_zero']
        · exact W.zero_mem
        intro d hd
        rw [mem_support_iff, coeff_monomial_mul'] at hd
        split_ifs at hd with hmd
        · rw [memMf, not_le] at hm
          have hmd' : m.degree ≤ d.degree := by
            rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
            exact Finset.sum_le_sum fun i _ => hmd i
          omega
        · exact absurd rfl hd
    have hJW : ∀ p ∈ Jv, homogeneousComponent N p ∈ W := by
      intro p hp
      obtain ⟨a, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
      rw [map_sum]
      refine Submodule.sum_mem _ fun t _ => ?_
      rw [(a t).as_sum, Finset.sum_mul, map_sum]
      refine Submodule.sum_mem _ fun m _ => ?_
      have hmon : monomial m (coeff m (a t)) = coeff m (a t) • monomial m (1 : Ω) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [hmon, smul_mul_assoc, map_smul]
      exact W.smul_mem _ (hterm t m)
    intro f
    have hf : (f : Fin n →₀ ℕ).degree = N := (mem_finsuppAntidiag_univ_iff _).mp f.2
    have hmem : monomial (f : Fin n →₀ ℕ) (1 : Ω) ∈ W := by
      have h := hJW _ (hmono _ hf)
      rwa [homogeneousComponent_eq_self (isHomogeneous_monomial _ hf)] at h
    have h := hWle (Submodule.mem_map_of_mem hmem)
    convert h using 1
    ext f'
    simp only [π, LinearMap.pi_apply, lcoeff_apply, coeff_monomial, Pi.single_apply]
    by_cases hff : f' = f
    · subst hff
      simp
    · rw [if_neg hff, if_neg (fun h' => hff (Subtype.ext h'.symm))]
  obtain ⟨σ', hσ'⟩ := exists_det_submatrix_ne_zero (Mx.map φv) hspanv
  obtain ⟨D, hD⟩ : ∃ D, D = (Mx.submatrix id σ').det := ⟨_, rfl⟩
  have hDv : aeval v D ≠ 0 := by
    have h1 : φv D = ((Mx.map φv).submatrix id σ').det := by
      rw [hD]
      exact RingHom.map_det φv _
    have h2 : φv D = aeval v D := rfl
    rw [← h2, h1]
    exact hσ'
  have hDinc : D ∈ incIdeal Q k := by
    simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
    intro u hu
    obtain ⟨x, hx0, hxQ, hxu⟩ := hu
    let φu : MvPolynomial (Fin k × Fin n) F →+* AlgebraicClosure F :=
      (aeval u : MvPolynomial (Fin k × Fin n) F →ₐ[F] AlgebraicClosure F)
    have hφu : φu.comp (algebraMap F (MvPolynomial (Fin k × Fin n) F)) = algebraMap F (AlgebraicClosure F) :=
      AlgHom.comp_algebraMap _

    have hcol : ∀ p, eval₂ φu x (c p) = 0 := by
      rintro ⟨t, m, hm⟩
      rcases t with ⟨q, hq⟩ | i
      · have hqQ : homogeneousComponent N (monomial m 1 * q) ∈ Q :=
          hQ _ (Q.mul_mem_left _ (hSQ q hq)) N
        have h := hxQ _ hqQ
        simp only [c, G, Sum.elim_inl]
        rw [show monomial m (1 : MvPolynomial (Fin k × Fin n) F) *
            map (algebraMap F (MvPolynomial (Fin k × Fin n) F)) q =
            map (algebraMap F (MvPolynomial (Fin k × Fin n) F)) (monomial m 1 * q) by
          rw [map_mul, map_monomial, map_one (algebraMap F (MvPolynomial (Fin k × Fin n) F))], homogeneousComponent_map, eval₂_map, hφu, ← aeval_def]
        exact h
      · simp only [c, G, Sum.elim_inr]
        have hh : (monomial m (1 : MvPolynomial (Fin k × Fin n) F) *
            ∑ j, C (X (i, j)) * X j).IsHomogeneous (m.degree + 1) :=
          (isHomogeneous_monomial _ rfl).mul
            (IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)
        rw [homogeneousComponent_of_mem hh]
        split_ifs
        · rw [eval₂_mul, eval₂_sum]
          convert mul_zero _
          refine (Finset.sum_congr rfl fun j _ => ?_).trans (hxu i)
          simp [φu]
        · simp
    let w : Rows → AlgebraicClosure F := fun f => ∏ j, x j ^ (f : Fin n →₀ ℕ) j
    have hw0 : w ≠ 0 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hx0
      have hmemj : Finsupp.single j N ∈ Rows :=
        (mem_finsuppAntidiag_univ_iff _).mpr (Finsupp.degree_single _ _)
      intro hw
      have h := congrFun hw ⟨_, hmemj⟩
      simp only [w, Pi.zero_apply] at h
      rw [Fintype.prod_eq_single j (fun i hi => by simp [Finsupp.single_apply, Ne.symm hi])] at h
      simp only [Finsupp.single_eq_same] at h
      exact hj ((pow_eq_zero_iff (n := N) (by omega)).mp h)
    have hwM : Matrix.vecMul w ((Mx.map φu).submatrix id σ') = 0 := by
      funext p
      have h := hcol (σ' p)
      rw [eval₂_eq_sum_degree φu x _ (homogeneousComponent_isHomogeneous _ _)] at h
      simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Matrix.map_apply, id,
        Pi.zero_apply]
      refine (Finset.sum_congr rfl fun f _ => ?_).trans h
      exact mul_comm _ _
    have hdet := Matrix.exists_vecMul_eq_zero_iff.mp ⟨w, hw0, hwM⟩
    have h1 : φu D = ((Mx.map φu).submatrix id σ').det := by
      rw [hD]
      exact RingHom.map_det φu _
    have h2 : φu D = aeval u D := rfl
    rw [← h2, h1]
    exact hdet
  exact hDv (hv D hDinc)
end GroundTheory.Heights₂.Heights.IncidenceZeroLocus
