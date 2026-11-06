-- Prove2me | solution 1 for PfisterCEP.phase_sum_squeezing
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-06T02:10:28.657228+00:00
-- url     : https://prove2.me/submissions/f346934b-5298-43df-b858-f33a43f12f74

import Theorems.Thm_PfisterCEP_H3_quadrature_generator
import Theorems.Thm_PfisterCEP_hasDerivAt_smul_unique
import Definitions.Def_PfisterCEP_IsHeisenbergFlow

open PfisterCEP Filter
open scoped Topology

namespace PhaseSumProof

private theorem exp_decay {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t : ℝ => (Real.exp (-r * t) : ℂ)) atTop (𝓝 0) := by
  rw [← Complex.ofReal_zero, tendsto_ofReal_iff]
  exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hr))

section Derivative

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [ContinuousSMul ℂ E]
    {f g : ℝ → E} {f' g' : E} {t : ℝ}

omit [ContinuousSMul ℂ E] in
private theorem tvs_deriv_add (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun u => f u + g u) (f' + g') t := by
  apply HasFDerivAt.of_isLittleOTVS
  refine (hf.hasFDerivAt.isLittleOTVS.fun_add hg.hasFDerivAt.isLittleOTVS).congr_left ?_
  intro u
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_add]
  abel

omit [IsTopologicalAddGroup E] in
private theorem tvs_deriv_smul (c : ℂ) (hf : HasDerivAt f f' t) :
    HasDerivAt (fun u => c • f u) (c • f') t := by
  let L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  apply HasFDerivAt.of_isLittleOTVS
  refine (L.isBigOTVS_comp.trans_isLittleOTVS hf.hasFDerivAt.isLittleOTVS).congr_left ?_
  intro u
  simp only [Function.comp_apply, L, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_sub, smul_comm c (u - t)]

private theorem tvs_deriv_sub (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun u => f u - g u) (f' - g') t := by
  simpa only [sub_eq_add_neg, neg_one_smul] using tvs_deriv_add hf (tvs_deriv_smul (-1) hg)

end Derivative

private theorem decay_iff {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    (τ : ℝ → E →ₗ[ℂ] E) (r : ℝ) (hr : 0 < r)
    (P X O z : E) (p x : ℂ) (hO : O = p • P + x • X + z)
    (hP : ∀ t, τ t P = (Real.exp (-r * t) : ℂ) • P)
    (hX : ∀ t, τ t X = (Real.exp (r * t) : ℂ) • X)
    (hz : ∀ t, τ t z = z) :
    Tendsto (fun t => τ t O) atTop (𝓝 0) ↔ ∃ c : ℂ, O = c • P := by
  let d : ℝ → ℂ := fun t => (Real.exp (-r * t) : ℂ)
  let g : ℝ → ℂ := fun t => (Real.exp (r * t) : ℂ)
  have hd : Tendsto d atTop (𝓝 0) := exp_decay hr
  have horbit (t : ℝ) : τ t O = d t • (p • P) + g t • (x • X) + z := by
    rw [hO, map_add, map_add, map_smul, map_smul, hP, hX, hz]
    change p • (d t • P) + x • (g t • X) + z = _
    rw [smul_comm p (d t), smul_comm x (g t)]
  constructor
  · intro h
    have hdec : Tendsto (fun t => d t • (p • P)) atTop (𝓝 (0 : E)) := by
      simpa only [zero_smul] using hd.smul (tendsto_const_nhds (x := p • P))
    have hscaled : Tendsto
        (fun t => d t • (τ t O - d t • (p • P) - z)) atTop (𝓝 (0 : E)) := by
      simpa only [zero_smul] using hd.smul ((h.sub hdec).sub
        (tendsto_const_nhds (x := z)))
    have heval (t : ℝ) : d t • (τ t O - d t • (p • P) - z) = x • X := by
      have hmul : d t * g t = 1 := by
        dsimp [d, g]
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        simp [neg_mul]
      rw [horbit, show d t • (p • P) + g t • (x • X) + z - d t • (p • P) - z =
        g t • (x • X) by abel, smul_smul, hmul, one_smul]
    have hxzero : x • X = 0 :=
      tendsto_nhds_unique tendsto_const_nhds (by simpa only [heval] using hscaled)
    have hconst (t : ℝ) : τ t O - d t • (p • P) = z := by
      rw [horbit, hxzero, smul_zero, add_zero, add_sub_cancel_left]
    have hzzero : z = 0 :=
      tendsto_nhds_unique tendsto_const_nhds (by simpa only [hconst, sub_self] using h.sub hdec)
    exact ⟨p, by simpa only [hxzero, hzzero, add_zero] using hO⟩
  · rintro ⟨c, rfl⟩
    have hc : Tendsto (fun t => d t • P) atTop (𝓝 (0 : E)) := by
      simpa only [zero_smul] using hd.smul (tendsto_const_nhds (x := P))
    simpa only [map_smul, hP, smul_zero, d] using hc.const_smul c

private theorem split_mode {E : Type*} [AddCommGroup E] [Module ℂ E] {N : ℕ}
    (τ : ℝ → E →ₗ[ℂ] E) (b : Fin N → E) (hN : (N : ℂ) ≠ 0)
    (hfixed : ∀ (t : ℝ) (k l : Fin N), τ t (b k - b l) = b k - b l) (k : Fin N) :
    ∃ z : E, b k = (N : ℂ)⁻¹ • (∑ j, b j) + z ∧ ∀ t, τ t z = z := by
  let z : E := (N : ℂ)⁻¹ • ∑ j, (b k - b j)
  refine ⟨z, ?_, ?_⟩
  · calc
      b k = (N : ℂ)⁻¹ • ((N : ℂ) • b k) := by
        rw [smul_smul, inv_mul_cancel₀ hN, one_smul]
      _ = (N : ℂ)⁻¹ • (∑ j, b j) + z := by
        simp only [z, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_sub]
        abel
  · intro t
    simp only [z, map_smul, map_sum, hfixed]

end PhaseSumProof

open PhaseSumProof

theorem solution {A : Type*} [Ring A] [Algebra ℂ A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [ContinuousSMul ℂ A] [ContinuousSMul ℝ A] [T2Space A]
    [LocallyConvexSpace ℝ A] {N : ℕ} (a ad : Fin N → A) (hccr : IsCCR a ad)
    (ħ κ : ℝ) (hħ : ħ ≠ 0) (τ : ℝ → A →ₗ[ℂ] A)
    (hτ : IsHeisenbergFlow ħ (H3 ħ κ a ad) a ad τ) :
    (∀ t : ℝ, τ t (phaseSum a ad) = ((Real.exp (-(N * κ * t)) : ℝ) : ℂ) • phaseSum a ad) ∧
    (∀ t : ℝ, τ t (ampSum a ad) = ((Real.exp (N * κ * t) : ℝ) : ℂ) • ampSum a ad) ∧
    (∀ (t : ℝ) (k l : Fin N), τ t (ampQuad a ad k - ampQuad a ad l) = ampQuad a ad k - ampQuad a ad l) ∧
    (0 < κ → ∀ O ∈ Submodule.span ℂ (Set.range (ampQuad a ad) ∪ Set.range (phaseQuad a ad)),
      (Filter.Tendsto (fun t => τ t O) Filter.atTop (nhds 0) ↔ ∃ c : ℂ, O = c • phaseSum a ad)) ∧
    (κ < 0 → ∀ O ∈ Submodule.span ℂ (Set.range (ampQuad a ad) ∪ Set.range (phaseQuad a ad)),
      (Filter.Tendsto (fun t => τ t O) Filter.atTop (nhds 0) ↔ ∃ c : ℂ, O = c • ampSum a ad)) := by
  classical
  let D : A →ₗ[ℂ] A :=
    { toFun := heisenbergGen ħ (H3 ħ κ a ad)
      map_add' := by
        intro u v
        simp only [heisenbergGen, mul_add, add_mul, smul_sub, smul_add]
        abel
      map_smul' := by
        intro c u
        simp only [heisenbergGen, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← smul_sub]
        exact smul_comm _ _ _ }
  let P := phaseSum a ad
  let X := ampSum a ad
  let S := Submodule.span ℂ (Set.range (ampQuad a ad) ∪ Set.range (phaseQuad a ad))
  let r : ℝ := (N : ℝ) * κ
  have hmode (k : Fin N) (t : ℝ) :
      HasDerivAt (fun u => τ u (a k)) (τ t (D (a k))) t ∧
      HasDerivAt (fun u => τ u (ad k)) (τ t (D (ad k))) t := hτ.2 k t
  have hflow (O : A) (hO : O ∈ S) :
      τ 0 O = O ∧ ∀ t : ℝ, HasDerivAt (fun u => τ u O) (τ t (D O)) t := by
    refine Submodule.span_induction
      (p := fun O _ => τ 0 O = O ∧ ∀ t : ℝ, HasDerivAt (fun u => τ u O) (τ t (D O)) t)
      ?_ ?_ ?_ ?_ hO
    · rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · refine ⟨by simp only [ampQuad, map_add, (hτ.1 k).1, (hτ.1 k).2], ?_⟩
        intro t
        simpa only [ampQuad, map_add] using tvs_deriv_add (hmode k t).1 (hmode k t).2
      · refine ⟨by simp only [phaseQuad, map_smul, map_sub, (hτ.1 k).1, (hτ.1 k).2], ?_⟩
        intro t
        simpa only [phaseQuad, map_smul, map_sub] using
          tvs_deriv_smul Complex.I (tvs_deriv_sub (hmode k t).2 (hmode k t).1)
    · exact ⟨map_zero _, fun t => by
        simpa only [map_zero, zero_apply] using
          (hasFDerivAt_const (𝕜 := ℝ) (0 : A) t).hasDerivAt⟩
    · intro u v _ _ hu hv
      exact ⟨by rw [map_add, hu.1, hv.1], fun t => by
        simpa only [map_add] using tvs_deriv_add (hu.2 t) (hv.2 t)⟩
    · intro c u _ hu
      exact ⟨by rw [map_smul, hu.1], fun t => by
        simpa only [map_smul] using tvs_deriv_smul c (hu.2 t)⟩
  have hxmem (k : Fin N) : ampQuad a ad k ∈ S := Submodule.subset_span (Or.inl ⟨k, rfl⟩)
  have hpmem (k : Fin N) : phaseQuad a ad k ∈ S := Submodule.subset_span (Or.inr ⟨k, rfl⟩)
  have hXmem : X ∈ S := S.sum_mem (fun k _ => hxmem k)
  have hPmem : P ∈ S := S.sum_mem (fun k _ => hpmem k)
  have evolve (O : A) (hO : O ∈ S) (c : ℝ) (hc : D O = (c : ℂ) • O) (t : ℝ) :
      τ t O = (Real.exp (c * t) : ℂ) • O := by
    have hderiv (u : ℝ) :
        HasDerivAt (fun s => τ s O) ((c : ℂ) • τ u O) u := by
      simpa only [hc, map_smul] using (hflow O hO).2 u
    simpa only [(hflow O hO).1] using
      hasDerivAt_smul_unique (fun s => τ s O) c hderiv t
  have hgen := H3_quadrature_generator a ad hccr ħ κ hħ
  have hP (t : ℝ) : τ t P = (Real.exp (-r * t) : ℂ) • P :=
    evolve P hPmem (-r) hgen.1 t
  have hX (t : ℝ) : τ t X = (Real.exp (r * t) : ℂ) • X :=
    evolve X hXmem r hgen.2.1 t
  have hxdiff (t : ℝ) (k l : Fin N) :
      τ t (ampQuad a ad k - ampQuad a ad l) = ampQuad a ad k - ampQuad a ad l := by
    have h : D (ampQuad a ad k - ampQuad a ad l) = 0 := hgen.2.2.1 k l
    simpa using evolve _ (S.sub_mem (hxmem k) (hxmem l)) 0
      (by simpa only [Complex.ofReal_zero, zero_smul] using h) t
  have hpdiff (t : ℝ) (k l : Fin N) :
      τ t (phaseQuad a ad k - phaseQuad a ad l) = phaseQuad a ad k - phaseQuad a ad l := by
    have h : D (phaseQuad a ad k - phaseQuad a ad l) = 0 := hgen.2.2.2 k l
    simpa using evolve _ (S.sub_mem (hpmem k) (hpmem l)) 0
      (by simpa only [Complex.ofReal_zero, zero_smul] using h) t
  refine ⟨fun t => by simpa only [r, neg_mul] using hP t, hX, hxdiff, ?_⟩
  by_cases hN : N = 0
  · subst N
    have hS : S = ⊥ := by simp [S, Set.range_eq_empty]
    have hzero (O : A) (hO : O ∈ S) : O = 0 := by simpa [hS] using hO
    constructor <;> intro _ O hO <;> rw [hzero O hO]
    all_goals
      constructor
      · intro _
        exact ⟨0, by simp⟩
      · intro _
        simpa only [map_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : A)) atTop (𝓝 0))
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have split (O : A) (hO : O ∈ S) :
      ∃ p x : ℂ, ∃ z : A, O = p • P + x • X + z ∧ ∀ t, τ t z = z := by
    refine Submodule.span_induction
      (p := fun O _ => ∃ p x : ℂ, ∃ z : A, O = p • P + x • X + z ∧ ∀ t, τ t z = z)
      ?_ ?_ ?_ ?_ hO
    · rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · obtain ⟨z, hz, hf⟩ := split_mode τ (ampQuad a ad) hNc hxdiff k
        exact ⟨0, (N : ℂ)⁻¹, z, by simpa only [X, ampSum, zero_smul, zero_add] using hz, hf⟩
      · obtain ⟨z, hz, hf⟩ := split_mode τ (phaseQuad a ad) hNc hpdiff k
        exact ⟨(N : ℂ)⁻¹, 0, z, by simpa only [P, phaseSum, zero_smul, add_zero] using hz, hf⟩
    · exact ⟨0, 0, 0, by simp, fun _ => map_zero _⟩
    · rintro u v _ _ ⟨p, x, z, hu, hzu⟩ ⟨p', x', z', hv, hzv⟩
      refine ⟨p + p', x + x', z + z', ?_, fun t => by rw [map_add, hzu, hzv]⟩
      rw [hu, hv, add_smul, add_smul]
      abel
    · rintro c u _ ⟨p, x, z, hu, hz⟩
      refine ⟨c * p, c * x, c • z, ?_, fun t => by rw [map_smul, hz]⟩
      rw [hu, smul_add, smul_add, smul_smul, smul_smul]
  constructor
  · intro hκ O hO
    obtain ⟨p, x, z, he, hz⟩ := split O hO
    exact decay_iff τ r (mul_pos hNr hκ) P X O z p x he hP hX hz
  · intro hκ O hO
    obtain ⟨p, x, z, he, hz⟩ := split O hO
    exact decay_iff τ (-r) (neg_pos.mpr (mul_neg_of_pos_of_neg hNr hκ)) X P O z x p
      (by simpa only [add_comm (x • X) (p • P)] using he)
      (by simpa only [neg_neg] using hX) hP hz
