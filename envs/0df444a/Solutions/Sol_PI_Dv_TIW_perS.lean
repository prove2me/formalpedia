-- Prove2me | solution 1 for PI.Dv.TIW.perS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:25:40.175918+00:00
-- url     : https://prove2.me/submissions/c4a54314-1a82-4bb0-bbf1-c1fa563b38bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TraceMemOfIntR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_PerS
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_TIW_absorb_eps
import Theorems.Thm_PI_Dv_TIW_card_H_pos
import Theorems.Thm_PI_Dv_TIW_dual_span
import Theorems.Thm_PI_Dv_TIW_epsS_eq_smul
import Theorems.Thm_PI_Dv_TIW_exists_dual_one
import Theorems.Thm_PI_Dv_TIW_intR_epsS
import Theorems.Thm_PI_Dv_TIW_intR_mul
import Theorems.Thm_PI_Dv_TIW_intR_of
import Theorems.Thm_PI_Dv_TIW_li_span_top
import Theorems.Thm_PI_Dv_TIW_mul_eS_eq
import Theorems.Thm_PI_Dv_TIW_rank_one_sandwich
import Theorems.Thm_PI_Dv_TIW_select_li
import Theorems.Thm_PI_Dv_TIW_span_orbit
import Theorems.Thm_PI_Dv_TIW_tau_eps_idem
import Theorems.Thm_PI_Dv_TIW_trace_mem_of_intR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.TIW
theorem _root_.solution (T : GoodSet K G) (P0 P : Pair K G) (hM1 : M1 T P0) (s : T.S) :
    ∃ (g g' : Fin (nS T P s) → G) (Γ : Matrix (Fin (nS T P s)) (Fin (nS T P s)) (𝓞 K)),
      (∀ j k, algebraMap (𝓞 K) K (Γ j k) = LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
        (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k))))) ∧
      Γ.det ≠ 0 ∧
      ∃ b' : Fin (nS T P s) → MonoidAlgebra K G,
        (∀ i, b' i * (eps P * eS T s) = eps P0 * eS T s * b' i * (eps P * eS T s)) ∧
        ∑ i, (epsS P * MonoidAlgebra.of K G (g i)) * b' i * (eps P * eS T s) = eps P * eS T s := by
  classical
  set τ := T.tau s with hτ
  set p := τ.asAlgebraHom (eps P) with hp_def
  set p0 := τ.asAlgebraHom (eps P0) with hp0_def
  have hp : p * p = p := tau_eps_idem τ P
  have hp0 : p0 * p0 = p0 := tau_eps_idem τ P0
  have h1 : Module.finrank K (LinearMap.range p0) = 1 := hM1 s
  set n := nS T P s with hn_def
  have hn : Module.finrank K (LinearMap.range p) = n := by rw [hn_def]; rfl
  clear_value n

  obtain ⟨v0', hv0ne, hv0⟩ := finrank_eq_one_iff'.mp h1
  set v0 : T.W s := v0'.1 with hv0_def
  have hv0ne' : v0 ≠ 0 := fun h => hv0ne (Subtype.ext h)
  have hpv0 : p0 v0 = v0 := by
    obtain ⟨w, hw⟩ := v0'.2
    rw [hv0_def, ← hw, ← Module.End.mul_apply, hp0]
  obtain ⟨f0, hf0⟩ := exists_dual_one (K := K) v0 hv0ne'
  have hline : ∀ w, p0 w = f0 (p0 w) • v0 := by
    intro w
    obtain ⟨c, hc⟩ := hv0 ⟨p0 w, LinearMap.mem_range_self _ _⟩
    have hc' : c • v0 = p0 w := congrArg Subtype.val hc
    rw [← hc', map_smul, hf0, smul_eq_mul, mul_one]

  let pc : T.W s →ₗ[K] LinearMap.range p := LinearMap.codRestrict _ p (fun w => LinearMap.mem_range_self p w)
  let F : G → LinearMap.range p := fun x => pc (τ x v0)
  have hF : Submodule.span K (Set.range F) = ⊤ := by
    have : Set.range F = pc '' Set.range (fun x => τ x v0) := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, span_orbit τ (T.irr s) v0 hv0ne', Submodule.map_top, LinearMap.range_eq_top]
    rintro ⟨u, w, rfl⟩
    exact ⟨w, rfl⟩
  obtain ⟨g0, hg0⟩ := select_li F hF
  let g : Fin n → G := g0 ∘ Fin.cast hn.symm
  have hg : LinearIndependent K (F ∘ g) := hg0.comp _ (Fin.cast_injective _)

  let ψ : G → Module.Dual K (LinearMap.range p) := fun x =>
    (f0 ∘ₗ p0 ∘ₗ τ x) ∘ₗ (LinearMap.range p).subtype
  have hψapp : ∀ x (u : LinearMap.range p), ψ x u = f0 (p0 (τ x u)) := fun x u => rfl
  have hψ : ∀ u : LinearMap.range p, (∀ x, ψ x u = 0) → u = 0 := by
    intro u hu
    by_contra hne
    have hne' : (u : T.W s) ≠ 0 := fun h => hne (Subtype.ext h)
    have hall : ∀ w, f0 (p0 w) = 0 := by
      intro w
      have hw : w ∈ Submodule.span K (Set.range fun x => τ x u) := by
        rw [span_orbit τ (T.irr s) u hne']; trivial
      induction hw using Submodule.span_induction with
      | mem y hy => obtain ⟨x, rfl⟩ := hy; exact hu x
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [map_smul, map_smul, hy, smul_zero]
    have := hall v0
    rw [hpv0, hf0] at this
    exact one_ne_zero this
  have hψspan := dual_span ψ hψ
  obtain ⟨g'0, hg'0⟩ := select_li ψ hψspan
  have hdn : Module.finrank K (Module.Dual K (LinearMap.range p)) = n := by
    rw [Subspace.dual_finrank_eq, hn]
  let g' : Fin n → G := g'0 ∘ Fin.cast hdn.symm
  have hg' : LinearIndependent K (ψ ∘ g') := hg'0.comp _ (Fin.cast_injective _)
  have hg'span : Submodule.span K (Set.range (ψ ∘ g')) = ⊤ := li_span_top _ hg' hdn.symm
  have hgspan : Submodule.span K (Set.range (F ∘ g)) = ⊤ := li_span_top _ hg hn.symm

  set cH : K := ((Nat.card P.H : ℕ) : K) with hcH
  set cH0 : K := ((Nat.card P0.H : ℕ) : K) with hcH0
  have hcH_ne : cH ≠ 0 := by rw [hcH]; exact_mod_cast (card_H_pos P).ne'
  have hcH0_ne : cH0 ≠ 0 := by rw [hcH0]; exact_mod_cast (card_H_pos P0).ne'
  have hτepsS : τ.asAlgebraHom (epsS P) = cH • p := by rw [epsS_eq_smul, map_smul]
  have hτepsS0 : τ.asAlgebraHom (epsS P0) = cH0 • p0 := by rw [epsS_eq_smul, map_smul]
  have hmem : ∀ j k, LinearMap.trace K (T.W s) (τ.asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k)))) ∈
        Set.range (algebraMap (𝓞 K) K) := fun j k =>
    trace_mem_of_intR τ _ (intR_mul (intR_mul (intR_epsS P0) (intR_of _)) (intR_mul (intR_epsS P) (intR_of _)))
  choose Γf hΓf using hmem
  let Γ : Matrix (Fin n) (Fin n) (𝓞 K) := Matrix.of Γf
  have hkey : ∀ j k, LinearMap.trace K (T.W s) (τ.asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k)))) =
        cH0 * cH * ψ (g' j) (F (g k)) := by
    intro j k
    set X := τ (g' j) * p * τ (g k) with hX
    have e1 : τ.asAlgebraHom (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g k))) =
        (cH0 * cH) • (p0 * X) := by
      rw [map_mul, map_mul, map_mul, hτepsS, hτepsS0, Representation.asAlgebraHom_of,
        Representation.asAlgebraHom_of, hX]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
      rw [mul_comm cH cH0]
    have e2 : LinearMap.trace K (T.W s) (p0 * X) = f0 (p0 (X v0)) := by
      have hs := rank_one_sandwich p0 hp0 h1 X
      have := congrArg (fun M : Module.End K (T.W s) => f0 (M v0)) hs
      simp only [Module.End.mul_apply, LinearMap.smul_apply, hpv0, map_smul, hf0, smul_eq_mul, mul_one] at this
      exact this.symm
    rw [e1, map_smul, e2, smul_eq_mul, hψapp]
    rfl
  let A : Matrix (Fin n) (Fin n) K := Matrix.of fun j k => ψ (g' j) (F (g k))
  have hΓK : Γ.map (algebraMap (𝓞 K) K) = (cH0 * cH) • A := by
    ext j k
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, A]
    show algebraMap (𝓞 K) K (Γf j k) = _
    exact (hΓf j k).trans (hkey j k)
  have hAdet : A.det ≠ 0 := by
    intro hA
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
    set w : LinearMap.range p := ∑ k, c k • F (g k) with hw
    have hψw : ∀ j, ψ (g' j) w = 0 := by
      intro j
      have := congrFun hc j
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, A, Pi.zero_apply] at this
      rw [hw, map_sum]
      simp only [map_smul, smul_eq_mul]
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hall : ∀ φ : Module.Dual K (LinearMap.range p), φ w = 0 := by
      intro φ
      have hφ : φ ∈ Submodule.span K (Set.range (ψ ∘ g')) := by rw [hg'span]; trivial
      induction hφ using Submodule.span_induction with
      | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hψw j
      | zero => rfl
      | add y z _ _ hy hz => rw [LinearMap.add_apply, hy, hz, add_zero]
      | smul a y _ hy => rw [LinearMap.smul_apply, hy, smul_zero]
    have hw0 : w = 0 := (Module.forall_dual_apply_eq_zero_iff K w).mp hall
    have := Fintype.linearIndependent_iff.mp hg c (by rw [← hw0, hw]; rfl)
    exact hc0 (funext this)
  have hdetK : (Γ.map (algebraMap (𝓞 K) K)).det ≠ 0 := by
    rw [hΓK, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hcH0_ne hcH_ne)) hAdet
  have hdetΓ : Γ.det ≠ 0 := by
    intro h
    apply hdetK
    rw [show Γ.map (algebraMap (𝓞 K) K) = (algebraMap (𝓞 K) K).mapMatrix Γ from rfl, ← RingHom.map_det, h,
      map_zero]
  refine ⟨g, g', Γ, fun j k => hΓf j k, hdetΓ, ?_⟩

  set ΓK := Γ.map (algebraMap (𝓞 K) K) with hΓKd
  set δ := ΓK.det with hδ
  let b : Fin n → MonoidAlgebra K G := fun j => epsS P0 * MonoidAlgebra.of K G (g' j)
  let a : Fin n → MonoidAlgebra K G := fun k => epsS P * MonoidAlgebra.of K G (g k)
  let b' : Fin n → MonoidAlgebra K G := fun i => δ⁻¹ • ∑ j, ΓK.adjugate i j • b j
  have hbY : ∀ j, b j * (eps P * eS T s) = eps P0 * eS T s * b j * (eps P * eS T s) := by
    intro j
    have := absorb_eps T s P0 P (MonoidAlgebra.of K G (g' j))
    exact this.symm
  refine ⟨b', fun i => ?_, ?_⟩
  · simp only [b', smul_mul_assoc, Finset.sum_mul, mul_smul_comm, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hbY j]
  ·
    have hδ0 : δ ≠ 0 := hdetK
    have hbu : ∀ j k, τ.asAlgebraHom (b j) (F (g k) : T.W s) = (ΓK j k * cH⁻¹) • v0 := by
      intro j k
      have hΓ : ΓK j k = cH0 * cH * ψ (g' j) (F (g k)) := (hΓf j k).trans (hkey j k)
      have hb : τ.asAlgebraHom (b j) = cH0 • (p0 * τ (g' j)) := by
        simp only [b, map_mul, hτepsS0, Representation.asAlgebraHom_of, smul_mul_assoc]
      rw [hb, LinearMap.smul_apply, Module.End.mul_apply, hline (τ (g' j) _), smul_smul, hΓ]
      congr 1
      rw [hψapp]
      field_simp
    have hb'u : ∀ i k, τ.asAlgebraHom (b' i) (F (g k) : T.W s) =
        (cH⁻¹ * (1 : Matrix (Fin n) (Fin n) K) i k) • v0 := by
      intro i k
      simp only [b', map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, hbu, smul_smul,
        ← Finset.sum_smul]
      congr 1
      have hadj : ∑ j, ΓK.adjugate i j * ΓK j k = δ * (1 : Matrix (Fin n) (Fin n) K) i k := by
        have := congrFun (congrFun (Matrix.adjugate_mul ΓK) i) k
        rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
        exact this
      have : ∑ j, ΓK.adjugate i j * (ΓK j k * cH⁻¹) = (∑ j, ΓK.adjugate i j * ΓK j k) * cH⁻¹ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hadj]
      field_simp
    set Z' : Module.End K (T.W s) := ∑ i, τ.asAlgebraHom (a i) * τ.asAlgebraHom (b' i) with hZ'
    have hZk : ∀ k, Z' (F (g k) : T.W s) = (F (g k) : T.W s) := by
      intro k
      rw [hZ', LinearMap.sum_apply]
      simp only [Module.End.mul_apply, hb'u, map_smul]
      rw [Finset.sum_eq_single k (fun x _ hx => by rw [Matrix.one_apply_ne hx, mul_zero, zero_smul])
        (by simp), Matrix.one_apply_eq, mul_one]
      have ha : τ.asAlgebraHom (a k) = cH • (p * τ (g k)) := by
        simp only [a, map_mul, hτepsS, Representation.asAlgebraHom_of, smul_mul_assoc]
      rw [ha, LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hcH_ne, one_smul, Module.End.mul_apply]
      rfl
    have hrange : ∀ u ∈ LinearMap.range p, u ∈ Submodule.span K (Set.range fun k => (F (g k) : T.W s)) := by
      intro u hu
      have h2 : (⟨u, hu⟩ : LinearMap.range p) ∈ Submodule.span K (Set.range (F ∘ g)) := by
        rw [hgspan]; trivial
      have h3 := Submodule.mem_map_of_mem (f := (LinearMap.range p).subtype) h2
      rw [Submodule.map_span, ← Set.range_comp] at h3
      exact h3
    have hZsp : ∀ u ∈ Submodule.span K (Set.range fun k => (F (g k) : T.W s)), Z' u = u := by
      intro u hsp
      induction hsp using Submodule.span_induction with
      | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hZk k
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz]
      | smul c y _ hy => rw [map_smul, hy]
    have hZu : ∀ u ∈ LinearMap.range p, Z' u = u := fun u hu => hZsp u (hrange u hu)
    have hZ : τ.asAlgebraHom (∑ i, a i * b' i * eps P) = p := by
      rw [map_sum]
      simp only [map_mul]
      rw [← Finset.sum_mul, ← hZ']
      apply LinearMap.ext; intro w
      rw [Module.End.mul_apply, hZu _ (LinearMap.mem_range_self p w)]
    calc ∑ i, a i * b' i * (eps P * eS T s) = (∑ i, a i * b' i * eps P) * eS T s := by
          rw [Finset.sum_mul]; simp only [mul_assoc]
      _ = eps P * eS T s := mul_eS_eq T s _ _ (by rw [hZ])
end PI.Dv.TIW
