-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlowUpLocalChart_proof_fd5cbf2af6f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:04:38.065817+00:00
-- url     : https://prove2.me/submissions/5572ab32-3e85-490e-9ffa-ebe1262088b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpLocalChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_maximalIdeal_le_map_of_transcendental_c5afbfdca7b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_mul_eq_of_forall_algebraMap_3eea5ef56ccd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_newVar_7a8cf0aa599e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_iff_1286dd372173
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mul_newVar_sub_mem_8482d2e8e889
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
set_option maxHeartbeats 400000
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace BlowUpLocalChart
theorem _root_.solution : BlowUpLocalChart.Statement.{u} := by
  intro R _ _ K _ ι _ J _ P hP u G' y hy hG' hrel x hx hG G₀ _ hG₀ W₀ _ hW₀
  have : P.IsPrime := hP
  have hQ : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hQG' : (blowUpOf P u) ≤ G' := le_sup_left.trans hG'.1.2

  let g : (MRing ι R ⧸ P) →+* (MRing (extIdx ι J) R ⧸ (blowUpOf P u)) :=
    Ideal.Quotient.lift P ((Ideal.Quotient.mk (blowUpOf P u)).comp
      (liftForm (J := J) : MRing ι R →ₐ[R] MRing (extIdx ι J) R).toRingHom)
      (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr ((liftForm_mem_blowUpOf_iff P u p).mpr hp))
  have hg : ∀ p, g (Ideal.Quotient.mk P p) = Ideal.Quotient.mk (blowUpOf P u) (liftForm p) := fun p => rfl
  have hg_inj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hg, Ideal.Quotient.eq_zero_iff_mem, liftForm_mem_blowUpOf_iff] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hcomap : G₀ = W₀.comap g := by
    ext a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.mem_comap, hg]
    change p ∈ G₀.comap (Ideal.Quotient.mk P) ↔ liftForm p ∈ W₀.comap (Ideal.Quotient.mk (blowUpOf P u))
    rw [hG₀, hW₀]
    rfl
  let ρ : (MRing (extIdx ι J) R ⧸ (blowUpOf P u)) →+* Polynomial (MRing ι R ⧸ P) :=
    Ideal.Quotient.lift (blowUpOf P u) (aeval (blowUpSubst P u)).toRingHom (fun a ha => RingHom.mem_ker.mp ha)
  have hρ : ∀ F, ρ (Ideal.Quotient.mk (blowUpOf P u) F) = aeval (blowUpSubst P u) F := fun F => rfl
  have hρg : ρ.comp g = Polynomial.C := by
    refine RingHom.ext fun a => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [RingHom.comp_apply, hg, hρ, aeval_blowUpSubst_liftForm]
  let F := Localization.localRingHom G₀ W₀ g hcomap
  have hF : ∀ a, F (algebraMap _ (Localization.AtPrime G₀) a) =
      algebraMap _ (Localization.AtPrime W₀) (g a) := fun a => Localization.localRingHom_to_map _ _ _ _ _
  have hB_inj : Function.Injective (algebraMap (MRing (extIdx ι J) R ⧸ (blowUpOf P u)) (Localization.AtPrime W₀)) :=
    IsLocalization.injective (Localization.AtPrime W₀) W₀.primeCompl_le_nonZeroDivisors
  have hA_inj : Function.Injective (algebraMap (MRing ι R ⧸ P) (Localization.AtPrime G₀)) :=
    IsLocalization.injective (Localization.AtPrime G₀) G₀.primeCompl_le_nonZeroDivisors
  let ιA := (algebraMap (MRing (extIdx ι J) R ⧸ (blowUpOf P u)) (Localization.AtPrime W₀)).comp g
  have hιA : Function.Injective ιA := hB_inj.comp hg_inj
  have hF_inj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective G₀.primeCompl z
    have h2 := congrArg F (IsLocalization.mk'_spec (Localization.AtPrime G₀) a s)
    rw [map_mul, hz, zero_mul, hF] at h2
    have ha : a = 0 := hg_inj (hB_inj (by rw [map_zero, map_zero]; exact h2.symm))
    rw [ha]
    exact IsLocalization.mk'_zero _

  obtain ⟨j, hYj⟩ : ∃ j : J, (newVar j : MRing (extIdx ι J) R) ∉ G' := hrel none
  have huj : u j ∉ P := by
    intro h
    apply hYj
    apply hQG'
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_newVar,
      Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero, zero_mul]
  have hsj : Ideal.Quotient.mk (blowUpOf P u) (newVar j) ∈ W₀.primeCompl := by
    intro h
    apply hYj
    rw [← hW₀]
    exact h
  let sj : W₀.primeCompl := ⟨_, hsj⟩
  let w := algebraMap (MRing (extIdx ι J) R ⧸ (blowUpOf P u)) (Localization.AtPrime W₀) (Ideal.Quotient.mk (blowUpOf P u) (newVar j))
  have hw0 : w ≠ 0 := by
    intro h
    apply hYj
    apply hQG'
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hB_inj (by rw [map_zero]; exact h)
  let e : J → Localization.AtPrime W₀ := fun k => IsLocalization.mk' _ (Ideal.Quotient.mk (blowUpOf P u) (newVar k)) sj
  have he : ∀ k, e k * w =
      algebraMap (MRing (extIdx ι J) R ⧸ (blowUpOf P u)) (Localization.AtPrime W₀) (Ideal.Quotient.mk (blowUpOf P u) (newVar k)) :=
    fun k => IsLocalization.mk'_spec _ _ sj
  let C := Subring.closure (Set.range F ∪ Set.range e)
  have hFC : ∀ a, F a ∈ C := fun a => Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  have heC : ∀ k, e k ∈ C := fun k => Subring.subset_closure (Or.inr ⟨k, rfl⟩)
  let f : Localization.AtPrime G₀ →+* C := F.codRestrict C hFC
  have hf : ∀ a, (f a : Localization.AtPrime W₀) = F a := fun a => rfl

  have hden : ∀ d ∈ C, ∃ l : MRing ι R ⧸ P, l ≠ 0 ∧ ∃ b, ιA l * d = ιA b := by
    intro d hd
    induction hd using Subring.closure_induction with
    | mem d hd =>
      rcases hd with ⟨z, rfl⟩ | ⟨k, rfl⟩
      · obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective G₀.primeCompl z
        refine ⟨s, fun h => s.2 (h ▸ G₀.zero_mem), a, ?_⟩
        have h2 := congrArg F (IsLocalization.mk'_spec (Localization.AtPrime G₀) a s)
        rw [map_mul, hF, hF] at h2
        rw [mul_comm]
        exact h2
      · refine ⟨Ideal.Quotient.mk P (u j), fun h => huj (Ideal.Quotient.eq_zero_iff_mem.mp h),
          Ideal.Quotient.mk P (u k), ?_⟩
        apply mul_right_cancel₀ hw0
        have hr := Ideal.Quotient.eq.mpr (liftForm_mul_newVar_sub_mem P u j k)
        rw [map_mul, map_mul, ← hg, ← hg] at hr
        have hr' := congrArg (algebraMap _ (Localization.AtPrime W₀)) hr
        rw [map_mul, map_mul] at hr'
        rw [mul_assoc, he]
        exact hr'
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | one => exact ⟨1, one_ne_zero, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨l₁, hl₁, b₁, e₁⟩ := hx
      obtain ⟨l₂, hl₂, b₂, e₂⟩ := hy
      refine ⟨l₁ * l₂, mul_ne_zero hl₁ hl₂, l₂ * b₁ + l₁ * b₂, ?_⟩
      rw [map_mul, map_add, map_mul, map_mul, ← e₁, ← e₂]
      ring
    | neg x _ hx =>
      obtain ⟨l, hl, b, e₁⟩ := hx
      exact ⟨l, hl, -b, by rw [map_neg, ← e₁]; ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨l₁, hl₁, b₁, e₁⟩ := hx
      obtain ⟨l₂, hl₂, b₂, e₂⟩ := hy
      refine ⟨l₁ * l₂, mul_ne_zero hl₁ hl₂, b₁ * b₂, ?_⟩
      rw [map_mul, map_mul, ← e₁, ← e₂]
      ring

  have hpoly : ∀ p : Polynomial C, ∃ l : MRing ι R ⧸ P, l ≠ 0 ∧ ∃ q : Polynomial (MRing ι R ⧸ P),
      Polynomial.C (ιA l) * p.map C.subtype = q.map ιA := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p₁ p₂ h₁ h₂ =>
      obtain ⟨l₁, hl₁, q₁, e₁⟩ := h₁
      obtain ⟨l₂, hl₂, q₂, e₂⟩ := h₂
      refine ⟨l₁ * l₂, mul_ne_zero hl₁ hl₂, Polynomial.C l₂ * q₁ + Polynomial.C l₁ * q₂, ?_⟩
      rw [Polynomial.map_add, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_C, ← e₁, ← e₂, map_mul, Polynomial.C_mul]
      ring
    | monomial n c =>
      obtain ⟨l, hl, b, e₁⟩ := hden c c.2
      refine ⟨l, hl, Polynomial.monomial n b, ?_⟩
      rw [Polynomial.map_monomial, Polynomial.map_monomial, Polynomial.C_mul_monomial]
      exact congrArg _ e₁

  have hu_nzd : Ideal.Quotient.mk P (u j) ∈ nonZeroDivisors (MRing ι R ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (fun h => huj (Ideal.Quotient.eq_zero_iff_mem.mp h))
  have hinj : Function.Injective (Polynomial.eval₂RingHom C.subtype w) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    obtain ⟨l, hl, q, e₁⟩ := hpoly p
    have h1 : (q.map ιA).eval w = 0 := by
      rw [← e₁, Polynomial.eval_mul, Polynomial.eval_map]
      simp only [Polynomial.coe_eval₂RingHom] at hp
      rw [hp, mul_zero]
    rw [Polynomial.eval_map] at h1
    have h2 : q.eval₂ g (Ideal.Quotient.mk (blowUpOf P u) (newVar j)) = 0 := by
      apply hB_inj
      rw [map_zero, Polynomial.hom_eval₂]
      exact h1
    have h3 := congrArg ρ h2
    rw [Polynomial.hom_eval₂, hρg, hρ, aeval_blowUpSubst_newVar, map_zero] at h3
    have hq : q = 0 := (Polynomial.comp_C_mul_X_eq_zero_iff hu_nzd).mp h3
    rw [hq, Polynomial.map_zero] at e₁
    have hl' : Polynomial.C (ιA l) ≠ 0 := by
      rw [Ne, Polynomial.C_eq_zero]
      exact fun h => hl (hιA (by rw [h, map_zero]))
    have h4 : p.map C.subtype = 0 := (mul_eq_zero.mp e₁).resolve_left hl'
    exact Polynomial.map_injective _ C.subtype_injective (by rw [h4, Polynomial.map_zero])

  let φ := Polynomial.eval₂RingHom C.subtype w
  have hB : ∀ z, ∃ a : Polynomial C, φ a = algebraMap (MRing (extIdx ι J) R ⧸ (blowUpOf P u)) (Localization.AtPrime W₀) z := by
    intro z
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction G using MvPolynomial.induction_on with
    | C r =>
      refine ⟨Polynomial.C (f (algebraMap _ _ (Ideal.Quotient.mk P (MvPolynomial.C r)))), ?_⟩
      simp only [φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Subring.coe_subtype, hf, hF, hg]
      congr 2
      simp [liftForm]
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add, map_add]⟩
    | mul_X p v hp =>
      obtain ⟨a, ha⟩ := hp
      rcases v with ⟨_ | k, i⟩
      · refine ⟨a * (Polynomial.C ⟨e i, heC i⟩ * Polynomial.X), ?_⟩
        rw [map_mul, ha, map_mul (Ideal.Quotient.mk _), map_mul (algebraMap _ _)]
        congr 1
        simp only [φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X, Subring.coe_subtype]
        exact he i
      · refine ⟨a * Polynomial.C (f (algebraMap _ _ (Ideal.Quotient.mk P (X ⟨k, i⟩)))), ?_⟩
        rw [map_mul, ha, map_mul (Ideal.Quotient.mk _), map_mul (algebraMap _ _)]
        congr 1
        simp only [φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Subring.coe_subtype, hf, hF, hg]
        congr 2
        simp [liftForm]
  have hsurj := exists_mul_eq_of_forall_algebraMap W₀ φ hB

  have hdim : ringKrullDim (Localization.AtPrime W₀) ≤ 1 := by
    have h0 : ringKrullDim (Localization.AtPrime W₀) = W₀.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height W₀ (Localization.AtPrime W₀)
    rw [h0]
    have h := Ideal.map_height_le_one_of_mem_minimalPrimes hG'
    rw [← hW₀, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
    exact_mod_cast h

  have hxG : liftForm x ∈ G' := hG.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  let c₀ : C := f (algebraMap _ _ (Ideal.Quotient.mk P x))
  have hc₀ : (c₀ : Localization.AtPrime W₀) =
      algebraMap (MRing (extIdx ι J) R ⧸ (blowUpOf P u)) (Localization.AtPrime W₀) (Ideal.Quotient.mk (blowUpOf P u) (liftForm x)) := by
    simp only [c₀, hf, hF, hg]
  have hc₀ne : (c₀ : Localization.AtPrime W₀) ≠ 0 := by
    rw [hc₀]
    intro h
    apply hx
    rw [← liftForm_mem_blowUpOf_iff P u, ← Ideal.Quotient.eq_zero_iff_mem]
    exact hB_inj (by rw [map_zero]; exact h)
  have hc₀m : (c₀ : Localization.AtPrime W₀) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime W₀) := by
    rw [hc₀, IsLocalization.AtPrime.to_map_mem_maximal_iff _ W₀]
    change liftForm x ∈ W₀.comap (Ideal.Quotient.mk (blowUpOf P u))
    rw [hW₀]
    exact hxG
  refine ⟨C, f, ?_, ?_, ?_, maximalIdeal_le_map_of_transcendental hdim C w hinj hsurj c₀ hc₀ne hc₀m⟩
  · intro a b h
    exact hF_inj (congrArg Subtype.val h)
  · intro c
    obtain ⟨l, hl, b, e₁⟩ := hden c c.2
    refine ⟨algebraMap _ _ l, fun h => hl (hA_inj (by rw [h, map_zero])), algebraMap _ _ b, ?_⟩
    apply Subtype.ext
    rw [Subring.coe_mul, hf, hf, hF, hF]
    exact e₁.symm
  · intro s
    rw [hf, hF, hg]
end BlowUpLocalChart
end GroundTheory.Heights₂.Heights.NumbersDVR
