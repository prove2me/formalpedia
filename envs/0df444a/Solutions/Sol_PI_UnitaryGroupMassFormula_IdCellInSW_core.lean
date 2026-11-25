-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IdCellInSW.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:47.158944+00:00
-- url     : https://prove2.me/submissions/f7877db8-2717-4182-ab5e-213efa38351e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_ExistsSmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdentityCellTrace_AlgIdentity
import Theorems.Thm_PI_UnitaryGroupMassFormula_IdCellInSW_alg_identity
import Theorems.Thm_PI_UnitaryGroupMassFormula_IdCellInSW_one_mul_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_PI_UnitaryGroupMassFormula_IdCellInSW_exists_retract
import Theorems.Thm_PI_UnitaryGroupMassFormula_IdCellInSW_exists_smul_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_IdCellInSW_riesz


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IdCellInSW
variable {E : Type} [Field E] [NumberField E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]
  [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
namespace PI.UnitaryGroupMassFormula.IdCellInSW
theorem _root_.solution (h : V →ₗ⋆[E] V →ₗ[E] E) (hs : h.IsSymm) (hnd : h.Nondegenerate)
    (Λ : Submodule (𝓞 E) V) (hfg : Λ.FG) (hsp : Submodule.span E (Λ : Set V) = ⊤)
    (hU : Formalism.HermitianLatticesTheory.dual h Λ = Λ)
    (X : Submodule E V) (hiso : ∀ x ∈ X, ∀ y ∈ X, h x y = 0) {r : ℕ}
    (e e' : Fin r → V) (he : ∀ a, e a ∈ X) (he' : ∀ a, e' a ∈ X)
    (c c' : Fin r → V → E)
    (hc : ∀ x ∈ X, x = ∑ a, c a x • e a) (hc' : ∀ x ∈ X, x = ∑ a, c' a x • e' a)
    (hcadd : ∀ a, ∀ x ∈ X, ∀ y ∈ X, c a (x + y) = c a x + c a y)
    (hcadd' : ∀ a, ∀ x ∈ X, ∀ y ∈ X, c' a (x + y) = c' a x + c' a y)
    (hcsmul : ∀ a (t : E), ∀ x ∈ X, c a (t • x) = t * c a x)
    (hcsmul' : ∀ a (t : E), ∀ x ∈ X, c' a (t • x) = t * c' a x)
    (hδ : ∀ a b, c a (e b) = if a = b then 1 else 0) (hδ' : ∀ a b, c' a (e' b) = if a = b then 1 else 0)
    (J : Fin r → Submodule (𝓞 E) E)
    (hJ1 : ∀ a, ∀ t ∈ J a, t • e a ∈ Λ ∧ t • e' a ∈ Λ)
    (hJ2 : ∀ x ∈ Λ, x ∈ X → ∀ a, c a x ∈ J a ∧ c' a x ∈ J a)
    (θ : 𝓞 E) (hθ : (θ : E) + star (θ : E) = 1) :
    ∃ n : V ≃ₗ[E] V, n ∈ Formalism.HermitianLatticesTheory.isom h ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ ∧ (∀ a, n (e a) = e' a) ∧
      ∀ v, (∀ x ∈ X, h x v = 0) → n v - v ∈ X := by
  classical

  have hl : ∀ (t : E) x y, h (t • x) y = star t * h x y := fun t x y => by
    rw [LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul]
  have hr : ∀ (t : E) x y, h x (t • y) = t * h x y := fun t x y => by
    rw [map_smul, smul_eq_mul]
  have hsy : ∀ x y, h y x = star (h x y) := fun x y => by
    rw [← hs.eq x y, starRingEnd_apply]
  have memΛ : ∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, h y x ∈ (1 : Submodule (𝓞 E) E) := fun x => by
    conv_lhs => rw [← hU]
    exact Formalism.HermitianLatticesTheory.dualBasic_mem_dual h Λ x
  have intΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, h x y ∈ (1 : Submodule (𝓞 E) E) := fun x hx y hy =>
    (memΛ y).1 hy x hx

  obtain ⟨ρ, hρX, hρid⟩ := exists_retract Λ hfg X
  let φ : Fin r → V → E := fun a x => c' a x - c a x
  have hφadd : ∀ a, ∀ x ∈ X, ∀ y ∈ X, φ a (x + y) = φ a x + φ a y := fun a x hx y hy => by
    simp only [φ, hcadd a x hx y hy, hcadd' a x hx y hy]; ring
  have hφsmul : ∀ a (t : E), ∀ x ∈ X, φ a (t • x) = t * φ a x := fun a t x hx => by
    simp only [φ, hcsmul a t x hx, hcsmul' a t x hx]; ring
  let ψ : Fin r → (Λ →ₗ[𝓞 E] E) := fun a =>
    { toFun := fun y => φ a (ρ y : V)
      map_add' := fun y₁ y₂ => by
        rw [map_add, Submodule.coe_add, hφadd a _ (hρX y₁) _ (hρX y₂)]
      map_smul' := fun o y => by
        rw [map_smul, Submodule.coe_smul, ← algebraMap_smul E o, hφsmul a _ _ (hρX y),
          RingHom.id_apply, Algebra.smul_def] }
  choose w hw using fun a => riesz h hs hnd Λ hfg hsp (ψ a)
  have hwX : ∀ a, ∀ x ∈ X, h (w a) x = φ a x := by
    intro a x hx
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem Λ hsp x
    have hdX : d • x ∈ X := by rw [← algebraMap_smul E d x]; exact X.smul_mem _ hx
    have h1 := hw a (d • x) hdx
    have h2 : ρ ⟨d • x, hdx⟩ = ⟨d • x, hdx⟩ := hρid _ hdX
    have h3 : ψ a ⟨d • x, hdx⟩ = φ a (d • x) := by
      show φ a (ρ ⟨d • x, hdx⟩ : V) = _
      rw [h2]
    rw [h3, ← algebraMap_smul E d x, hr, hφsmul a _ x hx] at h1
    exact mul_left_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd) h1
  have hwJ : ∀ a, ∀ y ∈ Λ, h (w a) y ∈ J a := by
    intro a y hy
    rw [hw a y hy]
    show φ a (ρ ⟨y, hy⟩ : V) ∈ J a
    have hm := hJ2 _ (ρ ⟨y, hy⟩).2 (hρX _) a
    exact (J a).sub_mem hm.2 hm.1

  have key : ∀ b, ∑ a, h (w a) (e' b) • e a = e b - e' b := by
    intro b
    have h1 : ∀ a, h (w a) (e' b) = (if a = b then 1 else 0) - c a (e' b) := fun a => by
      rw [hwX a _ (he' b)]
      simp only [φ, hδ' a b]
    simp only [h1, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hc _ (he' b)]

  let G : Fin r → Fin r → E := fun a b => h (w a) (w b)
  let k : Fin r → Fin r → E := fun a b => if a < b then -1 else if a = b then -(θ : E) else 0
  let s : Fin r → Fin r → E := fun a b => k a b * G a b
  have hkint : ∀ a b, k a b ∈ (1 : Submodule (𝓞 E) E) := by
    intro a b
    simp only [k]
    split_ifs
    · exact Submodule.mem_one.2 ⟨-1, by simp⟩
    · exact Submodule.mem_one.2 ⟨-θ, by simp⟩
    · exact Submodule.zero_mem _
  have hsG : ∀ a b, G a b + s a b + star (s b a) = 0 := by
    intro a b
    have hG : star (G b a) = G a b := (hsy (w b) (w a)).symm
    rcases lt_trichotomy a b with hab | rfl | hab
    · have h1 : ¬ b < a := not_lt.2 hab.le
      have h2 : b ≠ a := hab.ne'
      simp only [s, k, if_pos hab, if_neg h1, if_neg h2, zero_mul, star_zero]
      ring
    · have hGs : star (G a a) = G a a := hG
      simp only [s, k, lt_irrefl, if_false, if_true, star_mul', star_neg, hGs]
      linear_combination (-(G a a)) * hθ
    · have h1 : ¬ a < b := not_lt.2 hab.le
      have h2 : a ≠ b := hab.ne'
      simp only [s, k, if_pos hab, if_neg h1, if_neg h2, zero_mul, star_mul', star_neg, star_one, hG]
      ring

  let cc : Fin r → (V →ₗ[E] E) := fun a => -(h (w a)) + ∑ b, s a b • h (e b)
  have hcc : ∀ a v, cc a v = -h (w a) v + ∑ b, s a b * h (e b) v := fun a v => by
    simp [cc]
  let nL : V →ₗ[E] V :=
    LinearMap.id + ∑ a, (h (e a)).smulRight (w a) + ∑ a, (cc a).smulRight (e' a)
  have hn : ∀ v, nL v = v + ∑ a, h (e a) v • w a + ∑ a, cc a v • e' a := fun v => by
    simp [nL]
  have hBX : ∀ v, ∑ a, cc a v • e' a ∈ X := fun v =>
    X.sum_mem fun a _ => X.smul_mem _ (he' a)

  have K1 : ∀ v a, h (v + ∑ b, h (e b) v • w b) (e' a) = star (h (e a) v) := by
    intro v a
    have hk := congrArg (h v) (key a)
    rw [map_sum, map_sub] at hk
    simp only [hr] at hk
    rw [map_add, LinearMap.add_apply, LinearMap.map_sum₂]
    simp only [hl]
    have e1 : h v (e' a) = h v (e a) - ∑ b, h (w b) (e' a) * h v (e b) := by rw [hk]; ring
    rw [e1, ← hsy]
    have e2 : ∑ b, star (h (e b) v) * h (w b) (e' a) = ∑ b, h (w b) (e' a) * h v (e b) :=
      Finset.sum_congr rfl fun b _ => by rw [hsy (e b) v, mul_comm]
    rw [e2]
    ring

  have hiso_n : ∀ v v', h (nL v) (nL v') = h v v' := by
    intro v v'
    rw [hn, hn]
    set P := v + ∑ b, h (e b) v • w b with hP
    set P' := v' + ∑ b, h (e b) v' • w b with hP'
    have hBB : h (∑ a, cc a v • e' a) (∑ a, cc a v' • e' a) = 0 := hiso _ (hBX v) _ (hBX v')
    have hPB : h P (∑ a, cc a v' • e' a) = ∑ a, cc a v' * star (h (e a) v) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [hr, K1]
    have hBP : h (∑ a, cc a v • e' a) P' = ∑ a, star (cc a v) * h (e a) v' := by
      rw [LinearMap.map_sum₂]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hl, hsy P' (e' a), K1, star_star]
    have hPP : h P P' = h v v' + ((∑ a, h (e a) v' * star (h (w a) v)) +
        (∑ a, star (h (e a) v) * h (w a) v') +
        (∑ a, ∑ b, star (h (e a) v) * (h (e b) v' * G a b))) := by
      have e1 : ∀ a, h v (w a) = star (h (w a) v) := fun a => hsy _ _
      have hdbl : (∑ b, h (e b) v' * ∑ a, star (h (e a) v) * h (w a) (w b)) =
          ∑ a, ∑ b, star (h (e a) v) * (h (e b) v' * G a b) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by simp only [G]; ring
      rw [hP, hP']
      simp only [map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, e1, RingHom.id_apply, mul_add]
      rw [Finset.sum_add_distrib, hdbl]
      ring
    simp only [map_add, LinearMap.add_apply]
    rw [hBB, hPB, hBP, hPP]
    have := alg_identity (fun a => h (e a) v) (fun a => h (e a) v') (fun a => h (w a) v)
      (fun a => h (w a) v') G s hsG
    simp only [hcc]
    linear_combination this
  have hinj : Function.Injective nL := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine hnd.1 v fun y => ?_
    rw [← hiso_n v y, hv, LinearMap.map_zero₂]

  have P1 : ∀ a, ∀ v ∈ Λ, h (e a) v • w a ∈ Λ := by
    intro a v hv
    rw [memΛ]
    intro y hy
    rw [hr, hsy (w a) y]
    have ht := (hJ1 a _ (hwJ a y hy)).1
    have := intΛ _ ht v hv
    rw [hl] at this
    rwa [mul_comm]
  have P1' : ∀ a, ∀ v ∈ Λ, h (e' a) v • w a ∈ Λ := by
    intro a v hv
    rw [memΛ]
    intro y hy
    rw [hr, hsy (w a) y]
    have ht := (hJ1 a _ (hwJ a y hy)).2
    have := intΛ _ ht v hv
    rw [hl] at this
    rwa [mul_comm]
  have P2 : ∀ a, ∀ v ∈ Λ, cc a v • e' a ∈ Λ := by
    intro a v hv
    rw [memΛ]
    intro y hy
    rw [hr, hcc, hsy (e' a) y]
    have t1 : h (w a) v * star (h (e' a) y) ∈ (1 : Submodule (𝓞 E) E) := by
      have := intΛ _ (P1' a y hy) v hv
      rwa [hl, mul_comm] at this
    have t2 : ∀ b, s a b * h (e b) v * star (h (e' a) y) ∈ (1 : Submodule (𝓞 E) E) := by
      intro b
      have := intΛ _ (P1' a y hy) _ (P1 b v hv)
      rw [hl, hr] at this
      have e1 : s a b * h (e b) v * star (h (e' a) y) =
          k a b * (star (h (e' a) y) * (h (e b) v * h (w a) (w b))) := by simp only [s, G]; ring
      rw [e1]
      exact one_mul_mem (hkint a b) this
    rw [add_mul, Finset.sum_mul, neg_mul]
    exact Submodule.add_mem _ (Submodule.neg_mem _ t1) (Submodule.sum_mem _ fun b _ => t2 b)
  have hint : ∀ v ∈ Λ, nL v ∈ Λ := by
    intro v hv
    rw [hn]
    exact Λ.add_mem (Λ.add_mem hv (Λ.sum_mem fun a _ => P1 a v hv)) (Λ.sum_mem fun a _ => P2 a v hv)

  let n : V ≃ₗ[E] V := LinearEquiv.ofInjectiveEndo nL hinj
  have hnapp : ∀ v, n v = nL v := fun v => rfl
  refine ⟨n, ?_, ?_, ?_, ?_⟩
  · show ∀ x y, h (n x) (n y) = h x y
    intro x y
    rw [hnapp, hnapp, hiso_n]
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact hint v hv
    · intro y hy
      refine ⟨n.symm y, ?_, by simp⟩
      rw [SetLike.mem_coe, memΛ]
      intro x hx
      have e : h x (n.symm y) = h (nL x) y := by
        rw [← hiso_n x (n.symm y), ← hnapp (n.symm y), LinearEquiv.apply_symm_apply]
      rw [e]
      exact intΛ _ (hint x hx) y hy
  · intro a
    rw [hnapp, hn]
    have h0 : ∀ b, h (e b) (e a) = 0 := fun b => hiso _ (he b) _ (he a)
    have h1 : ∀ b, cc b (e a) = (if b = a then 1 else 0) - c' b (e a) := by
      intro b
      rw [hcc, hwX b _ (he a)]
      simp only [h0, mul_zero, Finset.sum_const_zero, add_zero, φ, hδ b a]
      ring
    simp only [h0, zero_smul, Finset.sum_const_zero, add_zero, h1, sub_smul, ite_smul, one_smul,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hc' _ (he a)]
    abel
  · intro v hv
    rw [hnapp, hn]
    have h0 : ∀ a, h (e a) v = 0 := fun a => hv _ (he a)
    simp only [h0, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
    exact hBX v
end PI.UnitaryGroupMassFormula.IdCellInSW
