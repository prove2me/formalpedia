-- Prove2me | solution 1 for TeschlQM.Algebraic.harmonic_oscillator
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T04:05:47.644704+00:00
-- url     : https://prove2.me/submissions/16d4e606-9a9d-4be6-b79f-c6d9c7025c22

import Mathlib
import Definitions.Def_TeschlQM_Shared_resolventSet
import Definitions.Def_TeschlQM_Algebraic_gaussCore
import Definitions.Def_TeschlQM_Algebraic_IsHarmonicOscillator
import Definitions.Def_TeschlQM_Algebraic_hermiteFunction

set_option autoImplicit false

namespace TeschlQM.Algebraic.HO4

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι : Type*}

lemma diag_memℓp (b : HilbertBasis ι ℂ E) (m : ι → ℂ) (C : ℝ) (hm : ∀ i, ‖m i‖ ≤ C) (x : E) :
    Memℓp (fun i => m i * b.repr x i) 2 := by
  refine Memℓp.mono (g := fun i => C * ‖b.repr x i‖) ?_ ?_
  · exact ((lp.memℓp (b.repr x)).norm).const_mul C
  · intro i
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _)

noncomputable def diagL (b : HilbertBasis ι ℂ E) (m : ι → ℂ) (C : ℝ) (hm : ∀ i, ‖m i‖ ≤ C) :
    E →ₗ[ℂ] E where
  toFun x := b.repr.symm ⟨fun i => m i * b.repr x i, diag_memℓp b m C hm x⟩
  map_add' x y := by
    rw [← map_add]
    congr 1
    ext i
    simp only [map_add, lp.coeFn_add, Pi.add_apply]
    rw [mul_add]
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    ext i
    simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

lemma repr_diagL (b : HilbertBasis ι ℂ E) (m : ι → ℂ) (C : ℝ) (hm : ∀ i, ‖m i‖ ≤ C) (x : E)
    (i : ι) : b.repr (diagL b m C hm x) i = m i * b.repr x i := by
  simp [diagL]

lemma norm_diagL_le (b : HilbertBasis ι ℂ E) (m : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ i, ‖m i‖ ≤ C) (x : E) : ‖diagL b m C hm x‖ ≤ C * ‖x‖ := by
  rw [← b.repr.norm_map (diagL b m C hm x), ← b.repr.norm_map x]
  have h1 : ‖b.repr (diagL b m C hm x)‖ ≤ ‖(C : ℂ) • b.repr x‖ := by
    refine lp.norm_mono (by norm_num) (fun i => ?_)
    rw [repr_diagL, lp.coeFn_smul, Pi.smul_apply, norm_mul, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _)
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC] at h1
  exact h1

noncomputable def diag (b : HilbertBasis ι ℂ E) (m : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ i, ‖m i‖ ≤ C) : E →L[ℂ] E :=
  (diagL b m C hm).mkContinuous C (norm_diagL_le b m C hC hm)

lemma repr_diag (b : HilbertBasis ι ℂ E) (m : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ i, ‖m i‖ ≤ C) (x : E) (i : ι) :
    b.repr (diag b m C hC hm x) i = m i * b.repr x i := by
  simp only [diag, LinearMap.mkContinuous_apply]
  exact repr_diagL b m C hm x i

lemma adjoint_antitone {S T : E →ₗ.[ℂ] E} (hS : Dense (S.domain : Set E))
    (hT : Dense (T.domain : Set E)) (h : S ≤ T) : T.adjoint ≤ S.adjoint := by
  have key : ∀ y : T.adjoint.domain, ∀ x : S.domain,
      inner ℂ (T.adjoint y) (x : E) = inner ℂ (y : E) (S x) := by
    intro y x
    have hx : (x : E) ∈ T.domain := h.1 x.2
    have e : S x = T ⟨x, hx⟩ := h.2 rfl
    rw [e]
    exact LinearPMap.adjoint_isFormalAdjoint hT y ⟨x, hx⟩
  refine ⟨fun y hy => LinearPMap.mem_adjoint_domain_of_exists y
      ⟨T.adjoint ⟨y, hy⟩, fun x => key ⟨y, hy⟩ x⟩, ?_⟩
  intro x y hxy
  symm
  apply LinearPMap.adjoint_apply_eq hS
  intro v
  rw [← hxy]
  exact key x v

theorem eigenbasis_selfAdjoint_spectrum (H : E →ₗ.[ℂ] E)
    (b : HilbertBasis ι ℂ E) (lam : ι → ℝ)
    (hdom : H.domain = Submodule.span ℂ (Set.range b))
    (hb : ∀ i, ∃ h : b i ∈ H.domain, H ⟨b i, h⟩ = (lam i : ℂ) • b i)
    (hfin : ∀ c : ℝ, {i | |lam i| ≤ c}.Finite) :
    IsSelfAdjoint H.closure ∧
      TeschlQM.Shared.spectrum H.closure = Set.range (fun i => ((lam i : ℝ) : ℂ)) := by
  classical
  have hD : Dense (H.domain : Set E) := by rw [hdom]; exact Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  set A := H.adjoint with hAdef
  -- coefficients of A y
  have K1 : ∀ (y : A.domain) (i : ι),
      inner ℂ (b i) (A y) = (lam i : ℂ) * inner ℂ (b i) (y : E) := by
    intro y i
    obtain ⟨hi, hHi⟩ := hb i
    have := LinearPMap.adjoint_isFormalAdjoint hD y ⟨b i, hi⟩
    rw [hHi, inner_smul_right] at this
    rw [← inner_conj_symm, this, map_mul, inner_conj_symm, Complex.conj_ofReal]
  -- membership criterion
  have K2 : ∀ y w : E, (∀ i, inner ℂ (b i) w = (lam i : ℂ) * inner ℂ (b i) y) →
      ∃ hy : y ∈ A.domain, A ⟨y, hy⟩ = w := by
    intro y w hw
    have hxw : ∀ x : H.domain, inner ℂ w (x : E) = inner ℂ y (H x) := by
      have P : ∀ v ∈ Submodule.span ℂ (Set.range b), ∀ hv : v ∈ H.domain,
          inner ℂ w v = inner ℂ y (H ⟨v, hv⟩) := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨i, rfl⟩ := hv
          intro hv'
          obtain ⟨hi, hHi⟩ := hb i
          have e : H ⟨b i, hv'⟩ = (lam i : ℂ) • b i := hHi
          rw [e, inner_smul_right, ← inner_conj_symm, hw i, map_mul, Complex.conj_ofReal,
            inner_conj_symm]
        | zero =>
          intro hv'
          have e : (⟨0, hv'⟩ : H.domain) = 0 := rfl
          rw [e, LinearPMap.map_zero, inner_zero_right, inner_zero_right]
        | add x z hx hz ihx ihz =>
          intro hv'
          have hx' : x ∈ H.domain := hdom ▸ hx
          have hz' : z ∈ H.domain := hdom ▸ hz
          have e : (⟨x + z, hv'⟩ : H.domain) = ⟨x, hx'⟩ + ⟨z, hz'⟩ := rfl
          rw [e, LinearPMap.map_add, inner_add_right, inner_add_right, ihx hx', ihz hz']
        | smul c x hx ihx =>
          intro hv'
          have hx' : x ∈ H.domain := hdom ▸ hx
          have e : (⟨c • x, hv'⟩ : H.domain) = c • ⟨x, hx'⟩ := rfl
          rw [e, LinearPMap.map_smul, inner_smul_right, inner_smul_right, ihx hx']
      intro x
      exact P x (hdom ▸ x.2) x.2
    have hy : y ∈ A.domain := LinearPMap.mem_adjoint_domain_of_exists y ⟨w, hxw⟩
    exact ⟨hy, LinearPMap.adjoint_apply_eq hD ⟨y, hy⟩ hxw⟩
  -- coefficients of H y
  have L0 : ∀ (y : H.domain) (i : ι),
      inner ℂ (b i) (H y) = (lam i : ℂ) * inner ℂ (b i) (y : E) := by
    have P : ∀ v ∈ Submodule.span ℂ (Set.range b), ∀ hv : v ∈ H.domain, ∀ i,
        inner ℂ (b i) (H ⟨v, hv⟩) = (lam i : ℂ) * inner ℂ (b i) v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        intro hv' i
        obtain ⟨hj, hHj⟩ := hb j
        have e : H ⟨b j, hv'⟩ = (lam j : ℂ) • b j := hHj
        rw [e, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j]
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      | zero =>
        intro hv' i
        have e : (⟨0, hv'⟩ : H.domain) = 0 := rfl
        rw [e, LinearPMap.map_zero, inner_zero_right, mul_zero]
      | add x z hx hz ihx ihz =>
        intro hv' i
        have hx' : x ∈ H.domain := hdom ▸ hx
        have hz' : z ∈ H.domain := hdom ▸ hz
        have e : (⟨x + z, hv'⟩ : H.domain) = ⟨x, hx'⟩ + ⟨z, hz'⟩ := rfl
        rw [e, LinearPMap.map_add, inner_add_right, inner_add_right, ihx hx' i, ihz hz' i,
          mul_add]
      | smul c x hx ihx =>
        intro hv' i
        have hx' : x ∈ H.domain := hdom ▸ hx
        have e : (⟨c • x, hv'⟩ : H.domain) = c • ⟨x, hx'⟩ := rfl
        rw [e, LinearPMap.map_smul, inner_smul_right, inner_smul_right, ihx hx' i]
        ring
    intro y i
    exact P y (hdom ▸ y.2) y.2 i
  -- H ≤ A
  have hHA : H ≤ A := by
    refine ⟨fun y hy => (K2 y (H ⟨y, hy⟩) (fun i => L0 ⟨y, hy⟩ i)).1, ?_⟩
    intro x y hxy
    obtain ⟨hy', e⟩ := K2 x (H x) (fun i => L0 x i)
    have : y = ⟨(x : E), hy'⟩ := Subtype.ext hxy.symm
    rw [this, e]
  have hDA : Dense (A.domain : Set E) := hD.mono hHA.1
  -- A symmetric
  have hsymm : A.IsFormalAdjoint A := by
    intro x y
    rw [← b.tsum_inner_mul_inner (A x) (y : E), ← b.tsum_inner_mul_inner (x : E) (A y)]
    congr 1
    funext i
    have e1 : inner ℂ (A x) (b i) = (lam i : ℂ) * inner ℂ (x : E) (b i) := by
      rw [← inner_conj_symm, K1, map_mul, Complex.conj_ofReal, inner_conj_symm]
    rw [e1, K1]
    ring
  have hAA : A.adjoint = A :=
    le_antisymm (adjoint_antitone hD hDA hHA) (hsymm.le_adjoint hDA)
  -- closure
  have hAclosed : A.IsClosed := LinearPMap.adjoint_isClosed hD
  have hcl : H.IsClosable := hAclosed.isClosable.leIsClosable hHA
  have hclA : H.closure = A := by
    apply le_antisymm
    · apply LinearPMap.le_of_le_graph
      rw [← hcl.graph_closure_eq_closure_graph]
      exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hHA) hAclosed
    · apply LinearPMap.le_of_le_graph
      rw [← hcl.graph_closure_eq_closure_graph]
      rintro ⟨x, z⟩ hxz
      rw [LinearPMap.mem_graph_iff] at hxz
      obtain ⟨y, hyx, hyz⟩ := hxz
      simp only at hyx hyz
      subst hyx hyz
      have hgen : ∀ i, ((b i : E), (lam i : ℂ) • b i) ∈ H.graph := by
        intro i
        obtain ⟨hi, hHi⟩ := hb i
        rw [LinearPMap.mem_graph_iff]
        exact ⟨⟨b i, hi⟩, rfl, hHi⟩
      let c : ι → ℂ := fun i => b.repr (y : E) i
      have hmem : ∀ s : Finset ι, (∑ i ∈ s, c i • ((b i : E), (lam i : ℂ) • b i)) ∈ H.graph :=
        fun s => Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hgen i))
      have hlim1 : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, c i • (b i : E))
          Filter.atTop (nhds (y : E)) := (b.hasSum_repr (y : E))
      have hlim2 : Filter.Tendsto (fun s : Finset ι => ∑ i ∈ s, c i • ((lam i : ℂ) • b i))
          Filter.atTop (nhds (A y)) := by
        have h2 := b.hasSum_repr (A y)
        have e : (fun i => b.repr (A y) i • b i) = fun i => c i • ((lam i : ℂ) • b i) := by
          funext i
          rw [b.repr_apply_apply, K1, smul_smul, mul_comm]
          simp only [c, b.repr_apply_apply]
        rw [e] at h2
        exact h2
      have hlim : Filter.Tendsto
          (fun s : Finset ι => ∑ i ∈ s, c i • ((b i : E), (lam i : ℂ) • b i))
          Filter.atTop (nhds ((y : E), A y)) := by
        have e : (fun s : Finset ι => ∑ i ∈ s, c i • ((b i : E), (lam i : ℂ) • b i)) =
            fun s => (∑ i ∈ s, c i • (b i : E), ∑ i ∈ s, c i • ((lam i : ℂ) • b i)) := by
          funext s
          ext <;> simp [Prod.fst_sum, Prod.snd_sum]
        rw [e]
        exact hlim1.prodMk_nhds hlim2
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  refine ⟨?_, ?_⟩
  · rw [hclA]
    exact LinearPMap.isSelfAdjoint_def.mpr hAA
  rw [hclA]
  ext z
  simp only [TeschlQM.Shared.spectrum, TeschlQM.Shared.resolventSet, Set.mem_compl_iff,
    Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · intro hz
    by_contra hnot
    apply hz
    push Not at hnot
    -- a uniform gap
    have hgap : ∃ δ > 0, ∀ i, δ ≤ ‖(lam i : ℂ) - z‖ := by
      set S := {i | |lam i| ≤ ‖z‖ + 1}
      have hpos : ∀ i, 0 < ‖(lam i : ℂ) - z‖ := fun i =>
        norm_pos_iff.mpr (sub_ne_zero.mpr (hnot i))
      have hfar : ∀ i, i ∉ S → 1 ≤ ‖(lam i : ℂ) - z‖ := by
        intro i hi
        simp only [S, Set.mem_ofPred_eq, not_le] at hi
        have h1 := norm_sub_norm_le ((lam i : ℂ)) z
        rw [Complex.norm_real, Real.norm_eq_abs] at h1
        linarith
      by_cases hS : S.Nonempty
      · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image S (fun i => ‖(lam i : ℂ) - z‖)
          (hfin _) hS
        refine ⟨min 1 ‖(lam a : ℂ) - z‖, lt_min one_pos (hpos a), fun i => ?_⟩
        by_cases hi : i ∈ S
        · exact (min_le_right _ _).trans (hmin i hi)
        · exact (min_le_left _ _).trans (hfar i hi)
      · refine ⟨1, one_pos, fun i => hfar i ?_⟩
        intro hi
        exact hS ⟨i, hi⟩
    obtain ⟨δ, hδ, hδi⟩ := hgap
    have hne : ∀ i, (lam i : ℂ) - z ≠ 0 := fun i h => by
      have := hδi i
      rw [h, norm_zero] at this
      linarith
    let m : ι → ℂ := fun i => ((lam i : ℂ) - z)⁻¹
    have hm : ∀ i, ‖m i‖ ≤ δ⁻¹ := by
      intro i
      simp only [m, norm_inv]
      exact inv_anti₀ hδ (hδi i)
    let R := diag b m δ⁻¹ (inv_nonneg.mpr hδ.le) hm
    have hR : ∀ x i, inner ℂ (b i) (R x) = m i * inner ℂ (b i) x := by
      intro x i
      rw [← b.repr_apply_apply, ← b.repr_apply_apply]
      exact repr_diag b m δ⁻¹ (inv_nonneg.mpr hδ.le) hm x i
    refine ⟨R, ?_, ?_⟩
    · intro φ
      obtain ⟨hy, e⟩ := K2 (R φ) (φ + z • R φ) (fun i => by
        rw [inner_add_right, inner_smul_right, hR]
        simp only [m]
        field_simp [hne i]
        ring)
      exact ⟨hy, by rw [e]; abel⟩
    · intro ψ
      apply b.repr.injective
      ext i
      rw [b.repr_apply_apply, b.repr_apply_apply, hR, inner_sub_right, inner_smul_right, K1]
      simp only [m]
      rw [← sub_mul, inv_mul_cancel_left₀ (hne i)]
  · rintro ⟨j, rfl⟩ ⟨R, _, hR2⟩
    have hwj : ∀ i, inner ℂ (b i) ((lam j : ℂ) • b j) = (lam i : ℂ) * inner ℂ (b i) (b j) := by
      intro i
      rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal i j]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    obtain ⟨hj, e⟩ := K2 (b j) ((lam j : ℂ) • b j) hwj
    have := hR2 ⟨b j, hj⟩
    rw [e, sub_self, map_zero] at this
    exact b.orthonormal.ne_zero j this.symm

end TeschlQM.Algebraic.HO4

namespace TeschlQM.Algebraic.HOH

open Polynomial MeasureTheory

/-- Physicists' Hermite polynomials by the recursion `H_{n+1} = 2X H_n - H_n'`. -/
noncomputable def hP : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => 2 * X * hP n - derivative (hP n)

lemma hP_zero : hP 0 = 1 := rfl

lemma hP_succ (n : ℕ) : hP (n + 1) = 2 * X * hP n - derivative (hP n) := rfl

lemma hP_deriv (n : ℕ) : derivative (hP (n + 1)) = 2 * ((n : ℝ[X]) + 1) * hP n := by
  induction n with
  | zero => simp [hP_succ, hP_zero]
  | succ n ih =>
    have hc : derivative (2 * ((n : ℝ[X]) + 1) * hP n) = 2 * ((n : ℝ[X]) + 1) * derivative (hP n) := by
      simp [derivative_mul]
    rw [hP_succ (n + 1), derivative_sub, derivative_mul, derivative_mul, ih, hc]
    simp only [derivative_ofNat, derivative_X, zero_mul, zero_add, mul_one]
    rw [hP_succ n]
    push_cast
    ring

lemma hP_ode (n : ℕ) :
    derivative (derivative (hP n)) = 2 * X * derivative (hP n) - 2 * (n : ℝ[X]) * hP n := by
  cases n with
  | zero => simp [hP_zero]
  | succ n =>
    have hc : derivative (2 * ((n : ℝ[X]) + 1) * hP n) = 2 * ((n : ℝ[X]) + 1) * derivative (hP n) := by
      simp [derivative_mul]
    rw [hP_deriv n, hc, hP_succ n]
    push_cast
    ring

lemma hasDerivAt_gauss (x : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s ^ 2)) (Real.exp (-x ^ 2) * (-(2 * x))) x := by
  have h0 := ((hasDerivAt_pow 2 x).const_mul (-1 : ℝ)).exp
  simp only [neg_one_mul, Nat.cast_ofNat] at h0
  norm_num at h0
  exact h0.congr_deriv (by ring)

lemma iter_gauss (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Real.exp (-y ^ 2)) =
      fun s => (-1) ^ n * Real.exp (-s ^ 2) * (hP n).eval s := by
  induction n with
  | zero => funext s; simp [hP_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have h3 : HasDerivAt (fun s => (-1) ^ n * Real.exp (-s ^ 2) * (hP n).eval s) _ s :=
      ((hasDerivAt_gauss s).const_mul ((-1 : ℝ) ^ n)).mul ((hP n).hasDerivAt s)
    rw [h3.deriv, hP_succ, eval_sub, eval_mul, eval_mul, eval_X, eval_ofNat]
    ring

lemma physHermite_eq (n : ℕ) (s : ℝ) : physHermite n s = (hP n).eval s := by
  unfold physHermite
  rw [iter_gauss]
  have h1 : Real.exp (s ^ 2) * Real.exp (-s ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : ((-1 : ℝ) ^ n) * ((-1) ^ n) = 1 := by
    rw [← mul_pow]; simp
  calc (-1) ^ n * Real.exp (s ^ 2) * ((-1) ^ n * Real.exp (-s ^ 2) * (hP n).eval s)
      = ((-1 : ℝ) ^ n * (-1) ^ n) * (Real.exp (s ^ 2) * Real.exp (-s ^ 2)) * (hP n).eval s := by
        ring
    _ = (hP n).eval s := by rw [h1, h2]; ring

lemma integrable_poly_gauss (Q : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    Integrable (fun s : ℝ => Q.eval s * Real.exp (-b * s ^ 2)) := by
  have e : (fun s : ℝ => Q.eval s * Real.exp (-b * s ^ 2)) = fun s =>
      ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * (s ^ (i : ℝ) * Real.exp (-b * s ^ 2)) := by
    funext s
    rw [eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.rpow_natCast]
    ring
  rw [e]
  refine integrable_finset_sum _ (fun i _ => ?_)
  refine (integrable_rpow_mul_exp_neg_mul_sq hb ?_).const_mul _
  have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
  linarith

lemma ipg (Q : ℝ[X]) : Integrable (fun s : ℝ => Q.eval s * Real.exp (-s ^ 2)) := by
  simpa using integrable_poly_gauss Q one_pos

lemma ibp (m n : ℕ) :
    ∫ s : ℝ, (hP m).eval s * (hP (n + 1)).eval s * Real.exp (-s ^ 2) =
      ∫ s : ℝ, (derivative (hP m)).eval s * (hP n).eval s * Real.exp (-s ^ 2) := by
  have hv : ∀ x : ℝ, HasDerivAt (fun s => (hP n).eval s * Real.exp (-s ^ 2))
      (-((hP (n + 1)).eval x * Real.exp (-x ^ 2))) x := by
    intro x
    have h : HasDerivAt (fun s => (hP n).eval s * Real.exp (-s ^ 2)) _ x :=
      ((hP n).hasDerivAt x).mul (hasDerivAt_gauss x)
    refine h.congr_deriv ?_
    rw [hP_succ, eval_sub, eval_mul, eval_mul, eval_X, eval_ofNat]
    ring
  have i1 : Integrable ((fun s => (hP m).eval s) *
      (fun s => -((hP (n + 1)).eval s * Real.exp (-s ^ 2)))) := by
    refine (ipg (-(hP m * hP (n + 1)))).congr (Filter.Eventually.of_forall (fun s => ?_))
    simp only [Pi.mul_apply, eval_neg, eval_mul]
    ring
  have i2 : Integrable ((fun s => (derivative (hP m)).eval s) *
      (fun s => (hP n).eval s * Real.exp (-s ^ 2))) := by
    refine (ipg (derivative (hP m) * hP n)).congr (Filter.Eventually.of_forall (fun s => ?_))
    simp only [Pi.mul_apply, eval_mul]
    ring
  have i3 : Integrable ((fun s => (hP m).eval s) *
      (fun s => (hP n).eval s * Real.exp (-s ^ 2))) := by
    refine (ipg (hP m * hP n)).congr (Filter.Eventually.of_forall (fun s => ?_))
    simp only [Pi.mul_apply, eval_mul]
    ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun s => (hP m).eval s) (u' := fun s => (derivative (hP m)).eval s)
    (v := fun s => (hP n).eval s * Real.exp (-s ^ 2))
    (v' := fun s => -((hP (n + 1)).eval s * Real.exp (-s ^ 2)))
    (fun x _ => (hP m).hasDerivAt x) (fun x _ => hv x) i1 i2 i3
  have e1 : (fun s => (hP m).eval s * (hP (n + 1)).eval s * Real.exp (-s ^ 2)) =
      fun s => -((hP m).eval s * -((hP (n + 1)).eval s * Real.exp (-s ^ 2))) := by
    funext s; ring
  rw [e1, integral_neg, key, neg_neg]
  congr 1
  funext s
  ring

lemma hP_orth (n : ℕ) : ∀ m : ℕ,
    ∫ s : ℝ, (hP m).eval s * (hP n).eval s * Real.exp (-s ^ 2) =
      if m = n then 2 ^ n * (n.factorial : ℝ) * Real.sqrt Real.pi else 0 := by
  induction n with
  | zero =>
    intro m
    cases m with
    | zero =>
      simp only [hP_zero, eval_one, one_mul, if_true, pow_zero, Nat.factorial_zero,
        Nat.cast_one]
      have := integral_gaussian 1
      simp only [neg_mul, one_mul, div_one] at this
      exact this
    | succ k =>
      have e : ∀ s : ℝ, (hP (k + 1)).eval s * (hP 0).eval s * Real.exp (-s ^ 2) =
          (hP 0).eval s * (hP (k + 1)).eval s * Real.exp (-s ^ 2) := fun s => by ring
      simp_rw [e]
      rw [ibp 0 k]
      simp [hP_zero]
  | succ n ih =>
    intro m
    cases m with
    | zero =>
      rw [ibp 0 n]
      simp [hP_zero]
    | succ k =>
      rw [ibp (k + 1) n, hP_deriv k]
      have e : ∀ s : ℝ, (2 * ((k : ℝ[X]) + 1) * hP k).eval s * (hP n).eval s * Real.exp (-s ^ 2) =
          (2 * ((k : ℝ) + 1)) * ((hP k).eval s * (hP n).eval s * Real.exp (-s ^ 2)) := fun s => by
        simp only [eval_mul, eval_add, eval_natCast, eval_one, eval_ofNat]
        ring
      simp_rw [e]
      rw [integral_const_mul, ih k]
      by_cases hkn : k = n
      · subst hkn
        simp only [if_true, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
        ring
      · have : k + 1 ≠ n + 1 := by omega
        simp [hkn, this]

end TeschlQM.Algebraic.HOH

namespace TeschlQM.Algebraic.HOH

open Polynomial MeasureTheory

/-- `t ↦ Q(t) e^{-ω t²/2}` as a complex function. -/
noncomputable def gQ (ω : ℝ) (Q : ℝ[X]) : ℝ → ℂ :=
  fun t => ((Q.eval t * Real.exp (-(ω * t ^ 2) / 2) : ℝ) : ℂ)

/-- `t ↦ t^k e^{-ω t²/2}`. -/
noncomputable def phi1 (ω : ℝ) (k : ℕ) : ℝ → ℂ :=
  fun x => ((x ^ k * Real.exp (-(ω * x ^ 2) / 2) : ℝ) : ℂ)

lemma gQ_add (ω : ℝ) (P Q : ℝ[X]) : gQ ω (P + Q) = gQ ω P + gQ ω Q := by
  funext t; simp only [gQ, eval_add, Pi.add_apply]; push_cast; ring

lemma gQ_C_mul (ω c : ℝ) (Q : ℝ[X]) : gQ ω (C c * Q) = (c : ℂ) • gQ ω Q := by
  funext t; simp only [gQ, eval_mul, eval_C, Pi.smul_apply, smul_eq_mul]; push_cast; ring

lemma gQ_mem (ω : ℝ) (Q : ℝ[X]) : gQ ω Q ∈ Submodule.span ℂ (Set.range (phi1 ω)) := by
  refine Polynomial.induction_on' Q (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [gQ_add]; exact add_mem hp hq
  · rw [← C_mul_X_pow_eq_monomial, gQ_C_mul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, ?_⟩)
    funext t; simp [gQ, phi1]

lemma hasDerivAt_E (ω t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(ω * s ^ 2) / 2))
      (Real.exp (-(ω * t ^ 2) / 2) * (-(ω * t))) t := by
  have h := ((hasDerivAt_pow 2 t).const_mul (-ω)).div_const 2
  have e : (fun y : ℝ => -ω * y ^ 2 / 2) = fun s => -(ω * s ^ 2) / 2 := by funext s; ring
  rw [e] at h
  exact h.exp.congr_deriv (by norm_num; ring)

/-- `D_ω Q = Q' - ω X Q`, so that `(gQ Q)' = gQ (D_ω Q)`. -/
noncomputable def Dw (ω : ℝ) (Q : ℝ[X]) : ℝ[X] := derivative Q - C ω * X * Q

lemma gQ_hasDerivAt (ω : ℝ) (Q : ℝ[X]) (t : ℝ) :
    HasDerivAt (gQ ω Q) (gQ ω (Dw ω Q) t) t := by
  have hR : HasDerivAt (fun s => Q.eval s * Real.exp (-(ω * s ^ 2) / 2)) _ t :=
    (Q.hasDerivAt t).mul (hasDerivAt_E ω t)
  refine hR.ofReal_comp.congr_deriv ?_
  simp only [gQ, Dw, eval_sub, eval_mul, eval_C, eval_X]
  push_cast; ring

lemma Dw_C_mul (ω c : ℝ) (Q : ℝ[X]) : Dw ω (C c * Q) = C c * Dw ω Q := by
  simp only [Dw, derivative_mul, derivative_C, zero_mul, zero_add] <;> ring

/-- `R_n(t) = H_n(√ω t)`. -/
noncomputable def Rn (ω : ℝ) (n : ℕ) : ℝ[X] := (hP n).comp (C (Real.sqrt ω) * X)

/-- normalization constant `(2ⁿ n!)^{-1/2} (ω/π)^{1/4}` -/
noncomputable def cn (ω : ℝ) (n : ℕ) : ℝ :=
  1 / Real.sqrt (2 ^ n * n.factorial) * (ω / Real.pi) ^ (1 / 4 : ℝ)

lemma hermite_eq (ω : ℝ) (n : ℕ) : hermiteFunction ω n = gQ ω (C (cn ω n) * Rn ω n) := by
  funext t
  simp only [hermiteFunction, gQ, cn, Rn, eval_mul, eval_C, eval_comp, eval_X, physHermite_eq]

lemma Rn_deriv (ω : ℝ) (n : ℕ) :
    derivative (Rn ω n) = C (Real.sqrt ω) * (derivative (hP n)).comp (C (Real.sqrt ω) * X) := by
  rw [Rn, derivative_comp, derivative_C_mul_X]

lemma Rn_deriv2 (ω : ℝ) (hω : 0 ≤ ω) (n : ℕ) :
    derivative (derivative (Rn ω n)) =
      2 * C ω * X * derivative (Rn ω n) - 2 * (n : ℝ[X]) * C ω * Rn ω n := by
  have hr : C (Real.sqrt ω) * C (Real.sqrt ω) = C ω := by
    rw [← C_mul, Real.mul_self_sqrt hω]
  rw [Rn_deriv, derivative_mul, derivative_C, zero_mul, zero_add, derivative_comp,
    derivative_C_mul_X, hP_ode]
  simp only [Rn, sub_comp, mul_comp, X_comp, natCast_comp, ofNat_comp]
  linear_combination (2 * C (Real.sqrt ω) * X * (derivative (hP n)).comp (C (Real.sqrt ω) * X)
    - 2 * (n : ℝ[X]) * (hP n).comp (C (Real.sqrt ω) * X)) * hr

lemma DwDw_Rn (ω : ℝ) (hω : 0 ≤ ω) (n : ℕ) :
    Dw ω (Dw ω (Rn ω n)) = (C ω) ^ 2 * X ^ 2 * Rn ω n - (2 * (n : ℝ[X]) + 1) * C ω * Rn ω n := by
  simp only [Dw, derivative_sub, derivative_mul, derivative_C, derivative_X, zero_mul, zero_add,
    mul_one]
  linear_combination Rn_deriv2 ω hω n

/-- The 1-D eigen-equation in derivative form. -/
lemma hermite_deriv2 (ω : ℝ) (hω : 0 ≤ ω) (n : ℕ) (t : ℝ) :
    HasDerivAt (hermiteFunction ω n) (gQ ω (Dw ω (C (cn ω n) * Rn ω n)) t) t ∧
    HasDerivAt (gQ ω (Dw ω (C (cn ω n) * Rn ω n)))
      (((ω ^ 2 * t ^ 2 - (2 * n + 1) * ω : ℝ) : ℂ) * hermiteFunction ω n t) t := by
  refine ⟨by rw [hermite_eq]; exact gQ_hasDerivAt ω _ t, ?_⟩
  refine (gQ_hasDerivAt ω _ t).congr_deriv ?_
  rw [Dw_C_mul, Dw_C_mul, DwDw_Rn ω hω n, hermite_eq]
  simp only [gQ, eval_mul, eval_sub, eval_C, eval_pow, eval_X, eval_add, eval_natCast,
    eval_ofNat, eval_one]
  push_cast
  ring

/-! ### spans -/

lemma hermite_mem (ω : ℝ) (n : ℕ) :
    hermiteFunction ω n ∈ Submodule.span ℂ (Set.range (phi1 ω)) := by
  rw [hermite_eq]; exact gQ_mem ω _

lemma X_mul_hP_mem (n : ℕ) : X * hP n ∈ Submodule.span ℝ (Set.range hP) := by
  cases n with
  | zero =>
    have e : X * hP 0 = (1 / 2 : ℝ) • hP 1 := by
      rw [smul_eq_C_mul, hP_succ, hP_zero]; simp only [derivative_one, sub_zero]
      rw [← mul_assoc, ← mul_assoc, ← C_ofNat, ← C_mul]; norm_num
    rw [e]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  | succ m =>
    have e : X * hP (m + 1) = (1 / 2 : ℝ) • hP (m + 2) + ((m : ℝ) + 1) • hP m := by
      rw [smul_eq_C_mul, smul_eq_C_mul, hP_succ (m + 1), hP_deriv m]
      have h2 : C (1 / 2 : ℝ) * 2 = 1 := by rw [← C_ofNat, ← C_mul]; norm_num
      have h3 : C ((m : ℝ) + 1) = (m : ℝ[X]) + 1 := by simp
      rw [h3]
      linear_combination (-(X * hP (m + 1) - (↑m + 1) * hP m)) * h2
    rw [e]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨m + 2, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))

lemma X_mul_mem (p : ℝ[X]) (hp : p ∈ Submodule.span ℝ (Set.range hP)) :
    X * p ∈ Submodule.span ℝ (Set.range hP) := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨n, rfl⟩ := hp; exact X_mul_hP_mem n
  | zero => rw [mul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [mul_add]; exact add_mem hp hq
  | smul c p _ hp => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hp

lemma X_pow_mem (k : ℕ) : (X : ℝ[X]) ^ k ∈ Submodule.span ℝ (Set.range hP) := by
  induction k with
  | zero => rw [pow_zero, ← hP_zero]; exact Submodule.subset_span ⟨0, rfl⟩
  | succ k ih => rw [pow_succ']; exact X_mul_mem _ ih

lemma cn_pos (ω : ℝ) (hω : 0 < ω) (n : ℕ) : 0 < cn ω n := by
  unfold cn
  have h1 : 0 < Real.sqrt (2 ^ n * n.factorial) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < (ω / Real.pi) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  positivity

lemma phi1_mem (ω : ℝ) (hω : 0 < ω) (k : ℕ) :
    phi1 ω k ∈ Submodule.span ℂ (Set.range (hermiteFunction ω)) := by
  set r := Real.sqrt ω with hr
  have hr0 : r ≠ 0 := (Real.sqrt_pos.mpr hω).ne'
  -- every `gQ ω (p.comp (C r * X))` with `p ∈ span hP` is in the span
  have key : ∀ p ∈ Submodule.span ℝ (Set.range hP),
      gQ ω (p.comp (C r * X)) ∈ Submodule.span ℂ (Set.range (hermiteFunction ω)) := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨n, rfl⟩ := hp
      have e : gQ ω ((hP n).comp (C r * X)) = ((cn ω n)⁻¹ : ℂ) • hermiteFunction ω n := by
        rw [hermite_eq, gQ_C_mul, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
          inv_mul_cancel₀ (cn_pos ω hω n).ne', Complex.ofReal_one, one_smul]
        rfl
      rw [e]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
    | zero =>
      have e : gQ ω ((0 : ℝ[X]).comp (C r * X)) = 0 := by funext t; simp [gQ]
      rw [e]; exact zero_mem _
    | add p q _ _ hp hq => rw [add_comp, gQ_add]; exact add_mem hp hq
    | smul c p _ hp =>
      rw [smul_eq_C_mul, mul_comp, C_comp, gQ_C_mul]
      exact Submodule.smul_mem _ _ hp
  have e : phi1 ω k = ((r ^ k)⁻¹ : ℂ) • gQ ω ((X ^ k).comp (C r * X)) := by
    funext t
    simp only [phi1, gQ, X_pow_comp, eval_pow, eval_mul, eval_C, eval_X, Pi.smul_apply,
      smul_eq_mul]
    push_cast
    have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0
    rw [mul_pow]
    field_simp
  rw [e]
  exact Submodule.smul_mem _ _ (key _ (X_pow_mem k))

/-! ### integrability and orthonormality -/

lemma gQ_sq_integrable (ω : ℝ) (hω : 0 < ω) (Q : ℝ[X]) :
    Integrable (fun t => ‖gQ ω Q t‖ ^ 2) := by
  refine (integrable_poly_gauss (Q * Q) hω).congr (Filter.Eventually.of_forall (fun t => ?_))
  simp only [gQ, eval_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
  ring_nf

lemma hermite_integral (ω : ℝ) (hω : 0 < ω) (k l : ℕ) :
    ∫ t : ℝ, starRingEnd ℂ (hermiteFunction ω k t) * hermiteFunction ω l t =
      if k = l then 1 else 0 := by
  set r := Real.sqrt ω with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hω
  have e1 : ∀ t : ℝ, starRingEnd ℂ (hermiteFunction ω k t) * hermiteFunction ω l t =
      ((cn ω k * cn ω l * ((hP k).eval (r * t) * (hP l).eval (r * t) *
        Real.exp (-(r * t) ^ 2)) : ℝ) : ℂ) := by
    intro t
    rw [hermite_eq, hermite_eq]
    simp only [gQ, Rn, eval_mul, eval_C, eval_comp, eval_X, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    congr 1
    have hsq : (r * t) ^ 2 = ω * t ^ 2 := by rw [mul_pow, hr, Real.sq_sqrt hω.le]
    rw [hsq]
    have : Real.exp (-(ω * t ^ 2) / 2) * Real.exp (-(ω * t ^ 2) / 2) = Real.exp (-(ω * t ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (cn ω k * cn ω l * (hP k).eval (r * t) * (hP l).eval (r * t)) * this
  simp_rw [e1]
  have hcomp := Measure.integral_comp_mul_left
    (fun s => (hP k).eval s * (hP l).eval s * Real.exp (-s ^ 2)) r
  rw [integral_complex_ofReal, integral_const_mul, hcomp, hP_orth l k]
  by_cases hkl : k = l
  · subst hkl
    simp only [if_true, smul_eq_mul]
    -- cn² · |1/r| · 2^k k! √π = 1
    have hc : cn ω k * cn ω k = 1 / (2 ^ k * k.factorial) * (r / Real.sqrt Real.pi) := by
      unfold cn
      have h4 : (ω / Real.pi) ^ (1 / 4 : ℝ) * (ω / Real.pi) ^ (1 / 4 : ℝ) =
          r / Real.sqrt Real.pi := by
        rw [← Real.rpow_add (by positivity), hr, ← Real.sqrt_div' ω (Real.pi_pos.le)
          , Real.sqrt_eq_rpow]
        norm_num
      have h5 : Real.sqrt (2 ^ k * k.factorial) * Real.sqrt (2 ^ k * k.factorial) =
          2 ^ k * k.factorial := Real.mul_self_sqrt (by positivity)
      calc 1 / Real.sqrt (2 ^ k * k.factorial) * (ω / Real.pi) ^ (1 / 4 : ℝ) *
            (1 / Real.sqrt (2 ^ k * k.factorial) * (ω / Real.pi) ^ (1 / 4 : ℝ))
          = 1 / (Real.sqrt (2 ^ k * k.factorial) * Real.sqrt (2 ^ k * k.factorial)) *
            ((ω / Real.pi) ^ (1 / 4 : ℝ) * (ω / Real.pi) ^ (1 / 4 : ℝ)) := by ring
        _ = _ := by rw [h4, h5]
    have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hf : (0 : ℝ) < 2 ^ k * k.factorial := by positivity
    have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
    have hr0' := hr0.ne'
    have hreal : cn ω k * cn ω k * (|r⁻¹| • (2 ^ k * (k.factorial : ℝ) * Real.sqrt Real.pi)) = 1 := by
      rw [hc, abs_of_pos (inv_pos.mpr hr0), smul_eq_mul]
      field_simp
    exact_mod_cast hreal
  · simp [hkl, Ne.symm hkl]

end TeschlQM.Algebraic.HOH

namespace TeschlQM.Algebraic.HOH

open Polynomial MeasureTheory

/-! ### three-dimensional products -/

lemma gQ_continuous (ω : ℝ) (Q : ℝ[X]) : Continuous (gQ ω Q) :=
  continuous_iff_continuousAt.mpr fun t => (gQ_hasDerivAt ω Q t).continuousAt

lemma phi1_eq_gQ (ω : ℝ) (k : ℕ) : phi1 ω k = gQ ω (X ^ k) := by
  funext t; simp [phi1, gQ]

lemma coord_continuous (j : Fin 3) :
    Continuous (fun x : EuclideanSpace ℝ (Fin 3) => x j) :=
  (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous

lemma prod_integrable {𝕜 : Type*} [RCLike 𝕜] (f : Fin 3 → ℝ → 𝕜) (hf : ∀ j, Integrable (f j)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, f j (x j)) := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  exact Integrable.fintype_prod hf

lemma prod_integral (f : Fin 3 → ℝ → ℂ) :
    ∫ x : EuclideanSpace ℝ (Fin 3), ∏ j, f j (x j) = ∏ j, ∫ t, f j t := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  exact integral_fintype_prod_volume_eq_prod f

lemma memLp_prod (f : Fin 3 → ℝ → ℂ) (hc : ∀ j, Continuous (f j))
    (hi : ∀ j, Integrable (fun t => ‖f j t‖ ^ 2)) :
    MemLp (fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, f j (x j)) 2 volume := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, f j (x j)) :=
    continuous_finset_prod _ (fun j _ => (hc j).comp (coord_continuous j))
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have e : (fun x : EuclideanSpace ℝ (Fin 3) => ‖∏ j, f j (x j)‖ ^ 2) =
      fun x => ∏ j, ‖f j (x j)‖ ^ 2 := by
    funext x; rw [norm_prod, Finset.prod_pow]
  rw [e]
  exact prod_integrable (fun j t => ‖f j t‖ ^ 2) hi

lemma gaussMonomial_prod (ω : ℝ) (α : Fin 3 → ℕ) :
    gaussMonomial 3 ω α = fun x => ∏ j, phi1 ω (α j) (x j) := by
  funext x
  simp only [gaussMonomial, phi1]
  rw [← Complex.ofReal_prod]
  congr 1
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, EuclideanSpace.norm_sq_eq]
  congr 2
  simp only [Real.norm_eq_abs, sq_abs, Finset.mul_sum, Finset.sum_div, Finset.sum_neg_distrib]
  rw [neg_div, Finset.sum_div]
  simp only [neg_div]
  rw [Finset.sum_neg_distrib]

lemma hermiteProduct_prod (ω : ℝ) (k : Fin 3 → ℕ) :
    hermiteProduct ω k = fun x => ∏ j, hermiteFunction ω (k j) (x j) := rfl

/-- slot-wise linearity -/
lemma slot {κ M : Type*} [AddCommGroup M] [Module ℂ M] (u : κ → (ℝ → ℂ)) (T : Submodule ℂ M)
    (L : (ℝ → ℂ) →ₗ[ℂ] M) (h : ∀ a, L (u a) ∈ T) (f : ℝ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range u)) : L f ∈ T := by
  have : Submodule.span ℂ (Set.range u) ≤ T.comap L :=
    Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact h a)
  exact this hf

noncomputable def L0 (g1 g2 : ℝ → ℂ) : (ℝ → ℂ) →ₗ[ℂ] (EuclideanSpace ℝ (Fin 3) → ℂ) where
  toFun f := fun x => f (x 0) * g1 (x 1) * g2 (x 2)
  map_add' f g := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

noncomputable def L1 (g0 g2 : ℝ → ℂ) : (ℝ → ℂ) →ₗ[ℂ] (EuclideanSpace ℝ (Fin 3) → ℂ) where
  toFun f := fun x => g0 (x 0) * f (x 1) * g2 (x 2)
  map_add' f g := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

noncomputable def L2 (g0 g1 : ℝ → ℂ) : (ℝ → ℂ) →ₗ[ℂ] (EuclideanSpace ℝ (Fin 3) → ℂ) where
  toFun f := fun x => g0 (x 0) * g1 (x 1) * f (x 2)
  map_add' f g := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma span3 {κ : Type*} (u : κ → (ℝ → ℂ)) (f : Fin 3 → ℝ → ℂ)
    (hf : ∀ j, f j ∈ Submodule.span ℂ (Set.range u)) :
    (fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, f j (x j)) ∈
      Submodule.span ℂ (Set.range (fun a : Fin 3 → κ =>
        fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, u (a j) (x j))) := by
  set T := Submodule.span ℂ (Set.range (fun a : Fin 3 → κ =>
        fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, u (a j) (x j)))
  have s2 : ∀ a0 a1, L2 (u a0) (u a1) (f 2) ∈ T := by
    intro a0 a1
    refine slot u T _ (fun a2 => Submodule.subset_span ⟨![a0, a1, a2], ?_⟩) (f 2) (hf 2)
    funext x
    simp [L2, Fin.prod_univ_three]
  have s1 : ∀ a0, L1 (u a0) (f 2) (f 1) ∈ T := by
    intro a0
    exact slot u T _ (fun a1 => s2 a0 a1) (f 1) (hf 1)
  have s0 : L0 (f 1) (f 2) (f 0) ∈ T := slot u T _ (fun a0 => s1 a0) (f 0) (hf 0)
  have e : (fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, f j (x j)) = L0 (f 1) (f 2) (f 0) := by
    funext x; simp [L0, Fin.prod_univ_three]
  rw [e]
  exact s0

lemma hermiteProduct_mem (ω : ℝ) (k : Fin 3 → ℕ) : hermiteProduct ω k ∈ coreFun 3 ω := by
  have h := span3 (phi1 ω) (fun j => hermiteFunction ω (k j)) (fun j => hermite_mem ω (k j))
  have e : (fun a : Fin 3 → ℕ => fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, phi1 ω (a j) (x j)) =
      gaussMonomial 3 ω := by
    funext a; rw [gaussMonomial_prod]
  rw [e] at h
  exact h

lemma gaussMonomial_mem (ω : ℝ) (hω : 0 < ω) (α : Fin 3 → ℕ) :
    gaussMonomial 3 ω α ∈ Submodule.span ℂ (Set.range (hermiteProduct ω)) := by
  have h := span3 (hermiteFunction ω) (fun j => phi1 ω (α j)) (fun j => phi1_mem ω hω (α j))
  rw [gaussMonomial_prod]
  exact h

lemma hermiteProduct_memLp (ω : ℝ) (hω : 0 < ω) (k : Fin 3 → ℕ) :
    MemLp (hermiteProduct ω k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  refine memLp_prod (fun j => hermiteFunction ω (k j)) (fun j => ?_) (fun j => ?_)
  · rw [hermite_eq]; exact gQ_continuous ω _
  · rw [hermite_eq]; exact gQ_sq_integrable ω hω _

lemma gaussMonomial_memLp' (ω : ℝ) (hω : 0 < ω) (α : Fin 3 → ℕ) :
    MemLp (gaussMonomial 3 ω α) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  rw [gaussMonomial_prod]
  refine memLp_prod (fun j => phi1 ω (α j)) (fun j => ?_) (fun j => ?_)
  · rw [phi1_eq_gQ]; exact gQ_continuous ω _
  · rw [phi1_eq_gQ]; exact gQ_sq_integrable ω hω _

lemma hermiteProduct_orth (ω : ℝ) (hω : 0 < ω) (k l : Fin 3 → ℕ) :
    ∫ x, starRingEnd ℂ (hermiteProduct ω k x) * hermiteProduct ω l x = if k = l then 1 else 0 := by
  have e : (fun x : EuclideanSpace ℝ (Fin 3) =>
      starRingEnd ℂ (hermiteProduct ω k x) * hermiteProduct ω l x) =
      fun x => ∏ j, (fun j t => starRingEnd ℂ (hermiteFunction ω (k j) t) *
        hermiteFunction ω (l j) t) j (x j) := by
    funext x
    simp only [hermiteProduct_prod, map_prod, ← Finset.prod_mul_distrib]
  rw [e, prod_integral (fun j t => starRingEnd ℂ (hermiteFunction ω (k j) t) *
    hermiteFunction ω (l j) t)]
  simp only [hermite_integral ω hω]
  by_cases hkl : k = l
  · subst hkl; simp
  · rw [if_neg hkl]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hkl
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

end TeschlQM.Algebraic.HOH

namespace TeschlQM.Algebraic.HOH

open Polynomial MeasureTheory

lemma gQ_contDiff (ω : ℝ) (Q : ℝ[X]) : ContDiff ℝ (⊤ : ℕ∞) (gQ ω Q) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Q.eval s) := by
    simpa [Polynomial.coe_aeval_eq_eval] using
      Polynomial.contDiff_aeval (𝕜 := ℝ) Q ((⊤ : ℕ∞) : WithTop ℕ∞)
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Q.eval s * Real.exp (-(ω * s ^ 2) / 2)) := by
    apply hp.mul
    apply Real.contDiff_exp.comp
    exact ((contDiff_const.mul (contDiff_id.pow 2)).neg).div_const 2
  exact Complex.ofRealCLM.contDiff.comp h1

lemma prod_contDiff (f : Fin 3 → ℝ → ℂ) (hf : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, f j (x j)) :=
  contDiff_prod (fun j _ => (hf j).comp
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff)

lemma gaussMonomial_contDiff' (ω : ℝ) (α : Fin 3 → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussMonomial 3 ω α) := by
  rw [gaussMonomial_prod]
  exact prod_contDiff _ (fun j => by rw [phi1_eq_gQ]; exact gQ_contDiff ω _)

lemma hermiteProduct_contDiff (ω : ℝ) (k : Fin 3 → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (hermiteProduct ω k) :=
  prod_contDiff _ (fun j => by rw [hermite_eq]; exact gQ_contDiff ω _)

/-- second derivative along a line -/
lemma second_line (F : EuclideanSpace ℝ (Fin 3) → ℂ) (hF : ContDiff ℝ 2 F)
    (x v : EuclideanSpace ℝ (Fin 3)) :
    iteratedFDeriv ℝ 2 F x (fun _ => v) = deriv (deriv (fun s : ℝ => F (x + s • v))) 0 := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hd1 : ∀ y, HasFDerivAt F (fderiv ℝ F y) y := fun y =>
    (hF.differentiable (by norm_num) y).hasFDerivAt
  have h1 : deriv (fun s : ℝ => F (x + s • v)) = fun s => fderiv ℝ F (x + s • v) v := by
    funext s
    exact ((hd1 _).comp_hasDerivAt s (hline s)).deriv
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hd2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    (hF1.differentiable one_ne_zero x).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => fderiv ℝ F (x + s • v)) (fderiv ℝ (fderiv ℝ F) x v) 0 :=
    hd2.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) (by simp)
  have h3 : HasDerivAt (fun s : ℝ => fderiv ℝ F (x + s • v) v)
      (fderiv ℝ (fderiv ℝ F) x v v) 0 := by
    have := h2.clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using this
  rw [h1, h3.deriv, iteratedFDeriv_two_apply]

lemma dd_shift (g g1 g2 : ℝ → ℂ) (h1 : ∀ t, HasDerivAt g (g1 t) t)
    (h2 : ∀ t, HasDerivAt g1 (g2 t) t) (a b : ℂ) (x0 : ℝ) :
    deriv (deriv (fun s : ℝ => a * g (x0 + s) * b)) 0 = a * g2 x0 * b := by
  have e1 : deriv (fun s : ℝ => a * g (x0 + s) * b) = fun s => a * g1 (x0 + s) * b := by
    funext s
    exact ((((h1 (x0 + s)).comp_const_add x0 s).const_mul a).mul_const b).deriv
  rw [e1]
  have := ((((h2 (x0 + 0)).comp_const_add x0 0).const_mul a).mul_const b).deriv
  rw [this, add_zero]

lemma lap_prod (f f1 f2 : Fin 3 → ℝ → ℂ) (hd1 : ∀ j t, HasDerivAt (f j) (f1 j t) t)
    (hd2 : ∀ j t, HasDerivAt (f1 j) (f2 j t) t)
    (hF : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, f j (x j)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    laplacian (fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, f j (x j)) x =
      f2 0 (x 0) * f 1 (x 1) * f 2 (x 2) + f 0 (x 0) * f2 1 (x 1) * f 2 (x 2) +
        f 0 (x 0) * f 1 (x 1) * f2 2 (x 2) := by
  unfold laplacian
  rw [Fin.sum_univ_three, second_line _ hF, second_line _ hF, second_line _ hF]
  have c0 : (fun s : ℝ => ∏ j, f j ((x + s • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) j)) =
      fun s => 1 * f 0 (x 0 + s) * (f 1 (x 1) * f 2 (x 2)) := by
    funext s; simp [Fin.prod_univ_three, EuclideanSpace.single_apply] <;> ring
  have c1 : (fun s : ℝ => ∏ j, f j ((x + s • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) j)) =
      fun s => f 0 (x 0) * f 1 (x 1 + s) * f 2 (x 2) := by
    funext s; simp [Fin.prod_univ_three, EuclideanSpace.single_apply] <;> ring
  have c2 : (fun s : ℝ => ∏ j, f j ((x + s • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) j)) =
      fun s => (f 0 (x 0) * f 1 (x 1)) * f 2 (x 2 + s) * 1 := by
    funext s; simp [Fin.prod_univ_three, EuclideanSpace.single_apply] <;> ring
  rw [c0, c1, c2, dd_shift _ _ _ (hd1 0) (hd2 0), dd_shift _ _ _ (hd1 1) (hd2 1),
    dd_shift _ _ _ (hd1 2) (hd2 2)]
  ring

lemma hermiteProduct_osc (ω : ℝ) (hω : 0 < ω) (k : Fin 3 → ℕ) :
    oscillatorAction ω (hermiteProduct ω k) =
      fun x => ((((2 * (k 0 + k 1 + k 2 : ℕ) + 3 : ℝ) * ω : ℝ) : ℂ) * hermiteProduct ω k x) := by
  funext x
  have hF : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin 3) => ∏ j, hermiteFunction ω (k j) (x j)) :=
    contDiff_infty.mp (hermiteProduct_contDiff ω k) 2
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  unfold oscillatorAction
  rw [hermiteProduct_prod]
  rw [lap_prod (fun j => hermiteFunction ω (k j))
    (fun j t => gQ ω (Dw ω (C (cn ω (k j)) * Rn ω (k j))) t)
    (fun j t => ((ω ^ 2 * t ^ 2 - (2 * (k j : ℕ) + 1) * ω : ℝ) : ℂ) * hermiteFunction ω (k j) t)
    (fun j t => (hermite_deriv2 ω hω.le (k j) t).1)
    (fun j t => (hermite_deriv2 ω hω.le (k j) t).2) hF x]
  simp only [Fin.prod_univ_three, hn]
  push_cast
  ring

end TeschlQM.Algebraic.HOH

namespace TeschlQM.Algebraic.HOE

open MeasureTheory TeschlQM.Algebraic TeschlQM.Algebraic.HOH
open scoped RealInnerProductSpace

/-- monomials `x ↦ x^α` on `ℝ³` -/
noncomputable def mono (α : Fin 3 → ℕ) : EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun x => ((∏ j, x j ^ α j : ℝ) : ℂ)

lemma mono_mul (α β : Fin 3 → ℕ) : mono α * mono β = mono (α + β) := by
  funext x
  simp only [mono, Pi.mul_apply, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  push_cast
  ring

lemma S_mul (f g : EuclideanSpace ℝ (Fin 3) → ℂ) (hf : f ∈ Submodule.span ℂ (Set.range mono))
    (hg : g ∈ Submodule.span ℂ (Set.range mono)) : f * g ∈ Submodule.span ℂ (Set.range mono) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨β, rfl⟩ := hg
      rw [mono_mul]; exact Submodule.subset_span ⟨_, rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add g1 g2 _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | smul c g _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact zero_mem _
  | add f1 f2 _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | smul c f _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

lemma inner_pow_mem (ξ : EuclideanSpace ℝ (Fin 3)) (n : ℕ) :
    (fun x : EuclideanSpace ℝ (Fin 3) => ((⟪ξ, x⟫ : ℝ) : ℂ) ^ n) ∈
      Submodule.span ℂ (Set.range mono) := by
  induction n with
  | zero =>
    have e : (fun x : EuclideanSpace ℝ (Fin 3) => ((⟪ξ, x⟫ : ℝ) : ℂ) ^ 0) = mono 0 := by
      funext x; simp [mono]
    rw [e]; exact Submodule.subset_span ⟨0, rfl⟩
  | succ n ih =>
    have hlin : (fun x : EuclideanSpace ℝ (Fin 3) => ((⟪ξ, x⟫ : ℝ) : ℂ)) ∈
        Submodule.span ℂ (Set.range mono) := by
      have e : (fun x : EuclideanSpace ℝ (Fin 3) => ((⟪ξ, x⟫ : ℝ) : ℂ)) =
          ((ξ 0 : ℝ) : ℂ) • mono ![1, 0, 0] + ((ξ 1 : ℝ) : ℂ) • mono ![0, 1, 0] +
            ((ξ 2 : ℝ) : ℂ) • mono ![0, 0, 1] := by
        funext x
        simp [mono, PiLp.inner_apply, Fin.sum_univ_three, Fin.prod_univ_three]
        ring
      rw [e]
      refine add_mem (add_mem ?_ ?_) ?_ <;>
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    have e : (fun x : EuclideanSpace ℝ (Fin 3) => ((⟪ξ, x⟫ : ℝ) : ℂ) ^ (n + 1)) =
        (fun x => ((⟪ξ, x⟫ : ℝ) : ℂ) ^ n) * (fun x => ((⟪ξ, x⟫ : ℝ) : ℂ)) := by
      funext x; simp [pow_succ]
    rw [e]; exact S_mul _ _ ih hlin

/-- the Gaussian weight `e^{-ω|x|²/2}` -/
noncomputable def gw (ω : ℝ) : EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun x => ((Real.exp (-(ω * ‖x‖ ^ 2) / 2) : ℝ) : ℂ)

lemma mul_gw_mem (ω : ℝ) (P : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hP : P ∈ Submodule.span ℂ (Set.range mono)) :
    (fun x => P x * gw ω x) ∈ coreFun 3 ω := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨α, rfl⟩ := hP
    have e : (fun x => mono α x * gw ω x) = gaussMonomial 3 ω α := by
      funext x; simp only [mono, gw, gaussMonomial]; push_cast; ring
    rw [e]; exact Submodule.subset_span ⟨α, rfl⟩
  | zero =>
    have e : (fun x : EuclideanSpace ℝ (Fin 3) => (0 : EuclideanSpace ℝ (Fin 3) → ℂ) x * gw ω x) = 0 := by
      funext x; simp
    rw [e]; exact zero_mem _
  | add P Q _ _ hP hQ =>
    have e : (fun x => (P + Q) x * gw ω x) = (fun x => P x * gw ω x) + (fun x => Q x * gw ω x) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [e]; exact add_mem hP hQ
  | smul c P _ hP =>
    have e : (fun x => (c • P) x * gw ω x) = c • (fun x => P x * gw ω x) := by
      funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact Submodule.smul_mem _ c hP

lemma core_int (ω : ℝ) (hω : 0 < ω) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (hg : MemLp g 2 volume)
    (horth : ∀ α, ∫ x, gaussMonomial 3 ω α x * g x = 0) :
    ∀ F ∈ coreFun 3 ω, Integrable (fun x => F x * g x) ∧ ∫ x, F x * g x = 0 := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨α, rfl⟩ := hF
    exact ⟨(gaussMonomial_memLp' ω hω α).integrable_mul hg, horth α⟩
  | zero => exact ⟨by simp, by simp⟩
  | add F G _ _ hF hG =>
    refine ⟨?_, ?_⟩
    · have := hF.1.add hG.1
      refine this.congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only [Pi.add_apply]; ring
    · have e : (fun x => (F + G) x * g x) = fun x => F x * g x + G x * g x := by
        funext x; simp only [Pi.add_apply]; ring
      rw [e, integral_add hF.1 hG.1, hF.2, hG.2, add_zero]
  | smul c F _ hF =>
    have e : (fun x => (c • F) x * g x) = fun x => c * (F x * g x) := by
      funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact ⟨hF.1.const_mul c, by rw [integral_const_mul, hF.2, mul_zero]⟩

/-- weighted integrability: `e^{c|x|} e^{-ω|x|²/2} |g|` is integrable -/
lemma weighted_int (ω : ℝ) (hω : 0 < ω) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (hg : MemLp g 2 volume)
    (c : ℝ) :
    Integrable (fun x => Real.exp (c * ‖x‖) * ‖gw ω x * g x‖) := by
  have hb := ((gaussMonomial_memLp' (ω / 2) (by positivity) 0).integrable_mul hg).norm
  have hb' := hb.const_mul (Real.exp (c ^ 2 / ω))
  refine hb'.mono' ?_ (Filter.Eventually.of_forall (fun x => ?_))
  · refine (Continuous.aestronglyMeasurable ?_).mul ?_
    · exact Real.continuous_exp.comp (continuous_const.mul continuous_norm)
    · refine (AEStronglyMeasurable.norm ?_)
      refine AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
      refine Continuous.aestronglyMeasurable ?_
      unfold gw
      fun_prop
  · have hgw : ‖gw ω x‖ = Real.exp (-(ω * ‖x‖ ^ 2) / 2) := by
      simp only [gw]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hgm : ‖gaussMonomial 3 (ω / 2) 0 x‖ = Real.exp (-(ω / 2 * ‖x‖ ^ 2) / 2) := by
      simp only [gaussMonomial, Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, Pi.mul_apply, norm_mul, hgw, hgm]
    have key : c * ‖x‖ + -(ω * ‖x‖ ^ 2) / 2 ≤ c ^ 2 / ω + -(ω / 2 * ‖x‖ ^ 2) / 2 := by
      rw [← sub_nonneg]
      have : c ^ 2 / ω + -(ω / 2 * ‖x‖ ^ 2) / 2 - (c * ‖x‖ + -(ω * ‖x‖ ^ 2) / 2) =
          (ω * ‖x‖ - 2 * c) ^ 2 / (4 * ω) := by
        field_simp; ring
      rw [this]; positivity
    have := Real.exp_le_exp.mpr key
    rw [Real.exp_add, Real.exp_add] at this
    calc Real.exp (c * ‖x‖) * (Real.exp (-(ω * ‖x‖ ^ 2) / 2) * ‖g x‖)
        = (Real.exp (c * ‖x‖) * Real.exp (-(ω * ‖x‖ ^ 2) / 2)) * ‖g x‖ := by ring
      _ ≤ (Real.exp (c ^ 2 / ω) * Real.exp (-(ω / 2 * ‖x‖ ^ 2) / 2)) * ‖g x‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = Real.exp (c ^ 2 / ω) * (Real.exp (-(ω / 2 * ‖x‖ ^ 2) / 2) * ‖g x‖) := by ring

/-- the Fourier transform of `e^{-ω|x|²/2} g` vanishes -/
lemma fourier_vanish (ω : ℝ) (hω : 0 < ω) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (hg : MemLp g 2 volume)
    (horth : ∀ α, ∫ x, gaussMonomial 3 ω α x * g x = 0) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ∫ v, Complex.exp (((-2 * Real.pi * ⟪ξ, v⟫ : ℝ) : ℂ) * Complex.I) * (gw ω v * g v) = 0 := by
  set h : EuclideanSpace ℝ (Fin 3) → ℂ := fun v => gw ω v * g v with hh
  set a : EuclideanSpace ℝ (Fin 3) → ℂ := fun v => ((-2 * Real.pi * ⟪ξ, v⟫ : ℝ) : ℂ) * Complex.I
  set F : ℕ → EuclideanSpace ℝ (Fin 3) → ℂ := fun n v => a v ^ n / (n.factorial : ℂ) * h v
  have hcore := core_int ω hω g hg horth
  have hFn : ∀ n, Integrable (F n) ∧ ∫ v, F n v = 0 := by
    intro n
    have hm := hcore _ (mul_gw_mem ω _ (inner_pow_mem ξ n))
    have e : F n = fun v => ((-2 * Real.pi : ℝ) * Complex.I) ^ n / (n.factorial : ℂ) *
        (((⟪ξ, v⟫ : ℝ) : ℂ) ^ n * gw ω v * g v) := by
      funext v; simp only [F, a, h]; push_cast; ring
    rw [e]
    exact ⟨hm.1.const_mul _, by rw [integral_const_mul, hm.2, mul_zero]⟩
  -- norms
  set c := 2 * Real.pi * ‖ξ‖
  have hnorm : ∀ n v, ‖F n v‖ ≤ (c * ‖v‖) ^ n / n.factorial * ‖h v‖ := by
    intro n v
    have hab : ‖a v‖ ≤ c * ‖v‖ := by
      show ‖((-2 * Real.pi * ⟪ξ, v⟫ : ℝ) : ℂ) * Complex.I‖ ≤ c * ‖v‖
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      calc |-2 * Real.pi * ⟪ξ, v⟫| = 2 * Real.pi * |⟪ξ, v⟫| := by
            rw [abs_mul, abs_mul, abs_neg, abs_two, abs_of_pos Real.pi_pos]
        _ ≤ 2 * Real.pi * (‖ξ‖ * ‖v‖) := by
            gcongr; exact abs_real_inner_le_norm ξ v
        _ = c * ‖v‖ := by ring
    show ‖a v ^ n / (n.factorial : ℂ) * h v‖ ≤ _
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    gcongr
  have hW := weighted_int ω hω g hg c
  have hsum : Summable (fun n => ∫ v, ‖F n v‖) := by
    refine summable_of_sum_range_le (fun n => integral_nonneg (fun v => norm_nonneg _))
      (c := ∫ v, Real.exp (c * ‖v‖) * ‖h v‖) (fun N => ?_)
    rw [← integral_finset_sum _ (fun n _ => (hFn n).1.norm)]
    refine integral_mono (integrable_finset_sum _ (fun n _ => (hFn n).1.norm)) hW (fun v => ?_)
    calc ∑ n ∈ Finset.range N, ‖F n v‖
        ≤ ∑ n ∈ Finset.range N, (c * ‖v‖) ^ n / n.factorial * ‖h v‖ :=
          Finset.sum_le_sum (fun n _ => hnorm n v)
      _ = (∑ n ∈ Finset.range N, (c * ‖v‖) ^ n / n.factorial) * ‖h v‖ := by
          rw [Finset.sum_mul]
      _ ≤ Real.exp (c * ‖v‖) * ‖h v‖ := by
          gcongr
          exact Real.sum_le_exp_of_nonneg (by positivity) N
  have htsum := integral_tsum_of_summable_integral_norm (fun n => (hFn n).1) hsum
  have hpt : ∀ v, ∑' n, F n v = Complex.exp (a v) * h v := by
    intro v
    simp only [F]
    rw [tsum_mul_right, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  simp_rw [hpt] at htsum
  have hz : ∀ n, ∫ v, F n v = 0 := fun n => (hFn n).2
  simp only [hz, tsum_zero] at htsum
  exact htsum.symm

lemma ae_zero (ω : ℝ) (hω : 0 < ω) (g : EuclideanSpace ℝ (Fin 3) → ℂ) (hg : MemLp g 2 volume)
    (horth : ∀ α, ∫ x, gaussMonomial 3 ω α x * g x = 0) : g =ᵐ[volume] 0 := by
  have hint : Integrable (fun v => gw ω v * g v) := by
    have := weighted_int ω hω g hg 0
    simp only [zero_mul, Real.exp_zero, one_mul] at this
    exact (integrable_norm_iff (AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable
      (by unfold gw; fun_prop)) hg.aestronglyMeasurable)).mp this
  have hF0 : ∀ x : EuclideanSpace ℝ (Fin 3),
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (EuclideanSpace ℝ (Fin 3))).flip
        (fun v => gw ω v * g v) x = 0 := by
    intro x
    refine Eq.trans ?_ (fourier_vanish ω hω g hg horth x)
    simp only [VectorFourier.fourierIntegral, LinearMap.flip_apply, Circle.smul_def,
      Real.fourierChar_apply, smul_eq_mul,
      show ∀ a b : EuclideanSpace ℝ (Fin 3), innerₗ (EuclideanSpace ℝ (Fin 3)) a b = ⟪a, b⟫ from
        fun a b => rfl]
    congr 1
    funext v
    congr 2
    push_cast
    ring
  have hzero : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))), gw ω x * g x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hint.locallyIntegrable ?_
    intro φ hφ hφs
    have hcs : HasCompactSupport (fun x => (φ x : ℂ)) := hφs.comp_left Complex.ofReal_zero
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
    let Φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ := hcs.toSchwartzMap hcd
    let Ψ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ := FourierTransform.fourierInv Φ
    have hΨ : FourierTransform.fourier Ψ = Φ := FourierInvPair.fourier_fourierInv_eq Φ
    have key := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (L := innerₗ (EuclideanSpace ℝ (Fin 3))) (μ := volume) (ν := volume)
      Real.continuous_fourierChar continuous_inner Ψ.integrable hint
    simp only [hF0, smul_zero, integral_zero] at key
    have e1 : ∀ ξ, VectorFourier.fourierIntegral Real.fourierChar volume
        (innerₗ (EuclideanSpace ℝ (Fin 3))) (Ψ : EuclideanSpace ℝ (Fin 3) → ℂ) ξ = (φ ξ : ℂ) := by
      intro ξ
      have := congrArg (fun F : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ => F ξ) hΨ
      exact this
    have e2 : (fun ξ => φ ξ • (gw ω ξ * g ξ)) = fun ξ => VectorFourier.fourierIntegral
        Real.fourierChar volume (innerₗ (EuclideanSpace ℝ (Fin 3)))
        (Ψ : EuclideanSpace ℝ (Fin 3) → ℂ) ξ • (gw ω ξ * g ξ) := by
      funext ξ
      rw [e1 ξ, Complex.real_smul, smul_eq_mul]
    rw [e2]
    exact key
  filter_upwards [hzero] with x hx
  have hne : gw ω x ≠ 0 := by simp [gw, Real.exp_ne_zero]
  exact (mul_eq_zero.mp hx).resolve_left hne

theorem core_dense' (ω : ℝ) (hω : 0 < ω) :
    Dense ((core 3 ω : Submodule ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))))) :
      Set (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  have horth : ∀ α, ∫ x, gaussMonomial 3 ω α x * (u : EuclideanSpace ℝ (Fin 3) → ℂ) x = 0 := by
    intro α
    have hmem : (gaussMonomial_memLp' ω hω α).toLp _ ∈ core 3 ω :=
      Submodule.subset_span ⟨α, (gaussMonomial_memLp' ω hω α).coeFn_toLp⟩
    have := (Submodule.mem_orthogonal _ _).mp hu _ hmem
    rw [MeasureTheory.L2.inner_def] at this
    rw [← this]
    apply integral_congr_ae
    filter_upwards [(gaussMonomial_memLp' ω hω α).coeFn_toLp] with x hx
    have hc : starRingEnd ℂ (gaussMonomial 3 ω α x) = gaussMonomial 3 ω α x :=
      Complex.conj_ofReal _
    rw [RCLike.inner_apply', hx, hc]
  have hz := ae_zero ω hω (u : EuclideanSpace ℝ (Fin 3) → ℂ) (Lp.memLp u) horth
  exact Lp.ext (hz.trans (Lp.coeFn_zero _ _ _).symm)

end TeschlQM.Algebraic.HOE

namespace TeschlQM.Algebraic.HOGlue

open MeasureTheory TeschlQM.Algebraic

/-- `L²(ℝ³)`. -/
noncomputable abbrev V3 := Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))

/-! ### Children (proved in the HOH / HOE sections above) -/

lemma gaussMonomial_contDiff (ω : ℝ) (α : Fin 3 → ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussMonomial 3 ω α) :=
  TeschlQM.Algebraic.HOH.gaussMonomial_contDiff' ω α

lemma gaussMonomial_memLp (ω : ℝ) (hω : 0 < ω) (α : Fin 3 → ℕ) :
    MemLp (gaussMonomial 3 ω α) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
  TeschlQM.Algebraic.HOH.gaussMonomial_memLp' ω hω α

lemma core_dense3 (ω : ℝ) (hω : 0 < ω) : Dense ((core 3 ω : Submodule ℂ V3) : Set V3) :=
  TeschlQM.Algebraic.HOE.core_dense' ω hω

lemma hermiteProduct_eigen (ω : ℝ) (hω : 0 < ω) :
    (∀ k : Fin 3 → ℕ, hermiteProduct ω k ∈ coreFun 3 ω) ∧
    (∀ k : Fin 3 → ℕ, oscillatorAction ω (hermiteProduct ω k) =
        fun x => ((((2 * (k 0 + k 1 + k 2 : ℕ) + 3 : ℝ) * ω : ℝ) : ℂ) * hermiteProduct ω k x)) ∧
    (∀ k : Fin 3 → ℕ,
        MemLp (hermiteProduct ω k) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) ∧
    (∀ k l : Fin 3 → ℕ, ∫ x, starRingEnd ℂ (hermiteProduct ω k x) * hermiteProduct ω l x =
        if k = l then 1 else 0) ∧
    (∀ α : Fin 3 → ℕ, gaussMonomial 3 ω α ∈ Submodule.span ℂ (Set.range (hermiteProduct ω))) :=
  ⟨TeschlQM.Algebraic.HOH.hermiteProduct_mem ω, TeschlQM.Algebraic.HOH.hermiteProduct_osc ω hω,
    TeschlQM.Algebraic.HOH.hermiteProduct_memLp ω hω, TeschlQM.Algebraic.HOH.hermiteProduct_orth ω hω,
    TeschlQM.Algebraic.HOH.gaussMonomial_mem ω hω⟩

/-! ### Glue -/

lemma coreFun_contDiff (ω : ℝ) (f : EuclideanSpace ℝ (Fin 3) → ℂ) (hf : f ∈ coreFun 3 ω) :
    ContDiff ℝ (⊤ : ℕ∞) f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨α, rfl⟩ := hf
    exact gaussMonomial_contDiff ω α
  | zero => exact contDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

lemma cd2 {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : EuclideanSpace ℝ (Fin 3)) : ContDiffAt ℝ (2 : ℕ) f x :=
  (contDiff_infty.mp hf 2).contDiffAt

lemma osc_add (ω : ℝ) {f g : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    oscillatorAction ω (f + g) = oscillatorAction ω f + oscillatorAction ω g := by
  have h : ∀ x, iteratedFDeriv ℝ 2 (f + g) x = iteratedFDeriv ℝ 2 f x + iteratedFDeriv ℝ 2 g x :=
    fun x => iteratedFDeriv_add_apply (cd2 hf x) (cd2 hg x)
  funext x
  simp only [oscillatorAction, laplacian, h, ContinuousMultilinearMap.add_apply,
    Finset.sum_add_distrib, Pi.add_apply]
  ring

lemma osc_smul (ω : ℝ) (c : ℂ) {f : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    oscillatorAction ω (c • f) = c • oscillatorAction ω f := by
  have h : ∀ x, iteratedFDeriv ℝ 2 (c • f) x = c • iteratedFDeriv ℝ 2 f x :=
    fun x => iteratedFDeriv_const_smul_apply (cd2 hf x)
  funext x
  simp only [oscillatorAction, laplacian, h, ContinuousMultilinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

lemma osc_zero (ω : ℝ) :
    oscillatorAction ω (0 : EuclideanSpace ℝ (Fin 3) → ℂ) = 0 := by
  have := osc_smul ω 0 (f := (0 : EuclideanSpace ℝ (Fin 3) → ℂ)) contDiff_const
  rw [zero_smul, zero_smul] at this
  exact this

lemma toLp_span {κ : Type*} (g : κ → (EuclideanSpace ℝ (Fin 3) → ℂ))
    (hg : ∀ j, MemLp (g j) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    ∀ f ∈ Submodule.span ℂ (Set.range g),
      ∃ hf : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))),
        hf.toLp f ∈ Submodule.span ℂ (Set.range (fun j => (hg j).toLp (g j))) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, rfl⟩ := hf
    exact ⟨hg j, Submodule.subset_span ⟨j, rfl⟩⟩
  | zero => exact ⟨MemLp.zero, by rw [MemLp.toLp_zero]; exact zero_mem _⟩
  | add f₁ f₂ _ _ ih₁ ih₂ =>
    obtain ⟨h₁, h₁'⟩ := ih₁
    obtain ⟨h₂, h₂'⟩ := ih₂
    exact ⟨h₁.add h₂, by rw [MemLp.toLp_add h₁ h₂]; exact add_mem h₁' h₂'⟩
  | smul c f _ ih =>
    obtain ⟨h, h'⟩ := ih
    exact ⟨h.const_smul c, by rw [MemLp.toLp_const_smul c h]; exact Submodule.smul_mem _ c h'⟩

lemma core_eq (ω : ℝ)
    (hGM : ∀ α, MemLp (gaussMonomial 3 ω α) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    core 3 ω = Submodule.span ℂ (Set.range (fun α => (hGM α).toLp (gaussMonomial 3 ω α))) := by
  unfold core
  congr 1
  ext ψ
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨α, Lp.ext (((hGM α).coeFn_toLp).trans hα.symm)⟩
  · rintro ⟨α, rfl⟩
    exact ⟨α, (hGM α).coeFn_toLp⟩

end TeschlQM.Algebraic.HOGlue

open TeschlQM.Algebraic MeasureTheory in
theorem solution (ω : ℝ) (hω : 0 < ω) :
    (∃ H, IsHarmonicOscillator ω H) ∧
      ∀ H, IsHarmonicOscillator ω H →
        IsSelfAdjoint H.closure ∧
          (∃ b : HilbertBasis (Fin 3 → ℕ) ℂ
              (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))),
            ∀ n : Fin 3 → ℕ,
              ((b n : Lp ℂ 2 volume) : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume]
                  hermiteProduct ω n ∧
                ∃ h : b n ∈ H.domain, ∃ E : ℂ, H ⟨b n, h⟩ = E • b n) ∧
          TeschlQM.Shared.spectrum H.closure = {z : ℂ | ∃ n : ℕ, z = ((2 * n + 3 : ℝ) * ω : ℝ)} := by
  classical
  obtain ⟨hmemF, heig, hL2, horth, hspan⟩ := HOGlue.hermiteProduct_eigen ω hω
  have hGM := HOGlue.gaussMonomial_memLp ω hω
  let v : (Fin 3 → ℕ) → HOGlue.V3 := fun k => (hL2 k).toLp (hermiteProduct ω k)
  have hv_ae : ∀ k, (v k : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume] hermiteProduct ω k :=
    fun k => (hL2 k).coeFn_toLp
  have hv_orth : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro k l
    rw [MeasureTheory.L2.inner_def, ← horth k l]
    apply integral_congr_ae
    filter_upwards [hv_ae k, hv_ae l] with x hk hl
    rw [RCLike.inner_apply', hk, hl]
  have hcore : core 3 ω = Submodule.span ℂ (Set.range v) := by
    rw [HOGlue.core_eq ω hGM]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨α, rfl⟩
      obtain ⟨hf, hmem⟩ := HOGlue.toLp_span (hermiteProduct ω) hL2 _ (hspan α)
      exact hmem
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨hf, hmem⟩ := HOGlue.toLp_span (gaussMonomial 3 ω) hGM _ (hmemF k)
      exact hmem
  have hsp : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
    rw [← hcore, (Submodule.dense_iff_topologicalClosure_eq_top).mp (HOGlue.core_dense3 ω hω)]
  let b := HilbertBasis.mk hv_orth hsp
  have hbv : ⇑b = v := HilbertBasis.coe_mk hv_orth hsp
  let lam : (Fin 3 → ℕ) → ℝ := fun k => (2 * ((k 0 + k 1 + k 2 : ℕ) : ℝ) + 3) * ω
  have hosc : ∀ k, oscillatorAction ω (hermiteProduct ω k) =
      fun x => ((lam k : ℝ) : ℂ) * hermiteProduct ω k x := fun k => heig k
  refine ⟨?_, ?_⟩
  · -- existence
    have hli : LinearIndependent ℂ v := hv_orth.linearIndependent
    let B := Module.Basis.span hli
    let Ev : (Fin 3 → ℕ) → HOGlue.V3 := fun k => ((lam k : ℝ) : ℂ) • v k
    let H : HOGlue.V3 →ₗ.[ℂ] HOGlue.V3 := ⟨Submodule.span ℂ (Set.range v), B.constr ℂ Ev⟩
    refine ⟨H, ?_⟩
    unfold IsHarmonicOscillator
    refine ⟨hcore.symm, ?_⟩
    have P : ∀ x ∈ Submodule.span ℂ (Set.range v), ∀ hx : x ∈ Submodule.span ℂ (Set.range v),
        ∃ f ∈ coreFun 3 ω, (x : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume] f ∧
          ((H (⟨x, hx⟩ : H.domain) : HOGlue.V3) : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume]
            oscillatorAction ω f := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        intro hx'
        refine ⟨hermiteProduct ω k, hmemF k, hv_ae k, ?_⟩
        have e1 : (⟨v k, hx'⟩ : Submodule.span ℂ (Set.range v)) = B k := by
          rw [Module.Basis.span_apply]
        have e2 : H (⟨v k, hx'⟩ : H.domain) = Ev k := by
          show B.constr ℂ Ev ⟨v k, hx'⟩ = Ev k
          rw [e1, Module.Basis.constr_basis]
        rw [e2, hosc k]
        filter_upwards [Lp.coeFn_smul ((lam k : ℝ) : ℂ) (v k), hv_ae k] with t h1 h2
        rw [h1, Pi.smul_apply, h2, smul_eq_mul]
      | zero =>
        intro hx'
        refine ⟨0, zero_mem _, Lp.coeFn_zero _ _ _, ?_⟩
        have e : (⟨0, hx'⟩ : H.domain) = 0 := rfl
        rw [e, LinearPMap.map_zero, HOGlue.osc_zero]
        exact Lp.coeFn_zero _ _ _
      | add x y hx hy ihx ihy =>
        intro hxy
        obtain ⟨f, hf, hxf, hHf⟩ := ihx hx
        obtain ⟨g, hg, hyg, hHg⟩ := ihy hy
        refine ⟨f + g, add_mem hf hg, ?_, ?_⟩
        · filter_upwards [Lp.coeFn_add x y, hxf, hyg] with t h1 h2 h3
          rw [h1, Pi.add_apply, h2, h3, Pi.add_apply]
        · have e : (⟨x + y, hxy⟩ : H.domain) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
          rw [e, LinearPMap.map_add, HOGlue.osc_add ω (HOGlue.coreFun_contDiff ω f hf) (HOGlue.coreFun_contDiff ω g hg)]
          filter_upwards [Lp.coeFn_add (H ⟨x, hx⟩) (H ⟨y, hy⟩), hHf, hHg] with t h1 h2 h3
          rw [h1, Pi.add_apply, h2, h3, Pi.add_apply]
      | smul c x hx ihx =>
        intro hcx
        obtain ⟨f, hf, hxf, hHf⟩ := ihx hx
        refine ⟨c • f, Submodule.smul_mem _ c hf, ?_, ?_⟩
        · filter_upwards [Lp.coeFn_smul c x, hxf] with t h1 h2
          rw [h1, Pi.smul_apply, h2, Pi.smul_apply]
        · have e : (⟨c • x, hcx⟩ : H.domain) = c • ⟨x, hx⟩ := rfl
          rw [e, LinearPMap.map_smul, HOGlue.osc_smul ω c (HOGlue.coreFun_contDiff ω f hf)]
          filter_upwards [Lp.coeFn_smul c (H ⟨x, hx⟩), hHf] with t h1 h2
          rw [h1, Pi.smul_apply, h2, Pi.smul_apply]
    rintro ⟨ψ, hψ⟩
    exact P ψ hψ hψ
  · intro H hH
    obtain ⟨hHdom, hHact⟩ := hH
    have hbk_ae : ∀ k, (b k : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume] hermiteProduct ω k := by
      intro k
      rw [hbv]
      exact hv_ae k
    have hb : ∀ k, ∃ h : b k ∈ H.domain, H ⟨b k, h⟩ = ((lam k : ℝ) : ℂ) • b k := by
      intro k
      have hk : b k ∈ H.domain := by
        rw [hHdom, hcore, hbv]
        exact Submodule.subset_span ⟨k, rfl⟩
      refine ⟨hk, ?_⟩
      obtain ⟨f, hf, hbf, hHf⟩ := hHact ⟨b k, hk⟩
      have hfeq : f = hermiteProduct ω k := by
        have hc1 : Continuous f := (HOGlue.coreFun_contDiff ω f hf).continuous
        have hc2 : Continuous (hermiteProduct ω k) :=
          (HOGlue.coreFun_contDiff ω _ (hmemF k)).continuous
        rw [← hc1.ae_eq_iff_eq volume hc2]
        exact hbf.symm.trans (hbk_ae k)
      subst hfeq
      apply Lp.ext
      refine hHf.trans ?_
      rw [hosc k]
      refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_smul ((lam k : ℝ) : ℂ) (b k)).symm
      filter_upwards [hbk_ae k] with t ht
      rw [Pi.smul_apply, ht, smul_eq_mul]
    have hdomb : H.domain = Submodule.span ℂ (Set.range b) := by rw [hHdom, hcore, hbv]
    have hfin : ∀ c : ℝ, {k | |lam k| ≤ c}.Finite := by
      intro c
      refine Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin 3 => Set.Iic ⌈c / ω⌉₊)
        (fun _ => Set.finite_Iic _)) ?_
      intro k hk
      rw [Set.mem_univ_pi]
      intro j
      have hk' : |lam k| ≤ c := hk
      have h1 : k j ≤ k 0 + k 1 + k 2 := by
        have := Fin.sum_univ_three k
        rw [← this]
        exact Finset.single_le_sum (fun i _ => Nat.zero_le (k i)) (Finset.mem_univ j)
      have h1' : (k j : ℝ) ≤ ((k 0 + k 1 + k 2 : ℕ) : ℝ) := by exact_mod_cast h1
      have h2 : (k j : ℝ) * ω ≤ lam k := by
        simp only [lam]
        nlinarith
      have h3 : (k j : ℝ) ≤ c / ω := by
        rw [le_div_iff₀ hω]
        linarith [le_abs_self (lam k)]
      have h4 := h3.trans (Nat.le_ceil (c / ω))
      show k j ≤ ⌈c / ω⌉₊
      exact_mod_cast h4
    obtain ⟨hSA, hspec⟩ := TeschlQM.Algebraic.HO4.eigenbasis_selfAdjoint_spectrum H b lam hdomb hb hfin
    refine ⟨hSA, ⟨b, fun n => ⟨hbk_ae n, (hb n).1, _, (hb n).2⟩⟩, ?_⟩
    rw [hspec]
    ext z
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k 0 + k 1 + k 2, rfl⟩
    · rintro ⟨n, rfl⟩
      refine ⟨fun j => if j = 0 then n else 0, ?_⟩
      simp [lam]
