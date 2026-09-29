-- Prove2me | solution 1 for Subalgebra.exists_ringHom_ringEquiv_adicCompletion_adjoin_div_of_flat_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/a7461551-0115-5b6f-9a34-922484061c0c

import Mathlib
import Theorems.Thm_Algebra_adjoin_div_tensorProduct_bijective_of_flat
import Theorems.Thm_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subalgebra_exists_ringHom_ringEquiv_adicCompletion_adjoin_div_of_flat_of_dense

set_option autoImplicit false

open IsLocalRing TensorProduct

set_option maxHeartbeats 6400000 in

theorem BCLG.levelwise
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (C : Subalgebra A K) (y : Ideal ↥C) (hy : y.IsMaximal) (J : Ideal ↥C)
    (a : ↥C) (haJ : a ∈ J) (ha0 : ((a : ↥C) : K) ≠ 0)
    (Ba : Subalgebra A K)
    (hBa : Ba = (Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A)
    (P : Ideal ↥Ba) (hP : P.IsMaximal)
    (hPy : ∀ (b : ↥C) (hb : ((b : ↥C) : K) ∈ Ba), (⟨_, hb⟩ : ↥Ba) ∈ P ↔ b ∈ y)
    (S : Type*) [CommRing S] (Ψ : ↥C →+* S)
    (hflat : letI : Algebra ↥C S := Ψ.toAlgebra; Module.Flat ↥C S)
    (𝔫 : Ideal S) (h𝔫 : Ideal.map Ψ y = 𝔫)
    (hdense : ∀ (n : ℕ) (s : S), ∃ c : ↥C, Ψ c - s ∈ 𝔫 ^ n)
    (hcomap : ∀ n : ℕ, Ideal.comap Ψ (𝔫 ^ n) = y ^ n)
    (𝔐 : Ideal S) (h𝔐 : Ideal.map Ψ J = 𝔐)
    (Φ : ↥Ba →+* Localization.Away (Ψ a))
    (hΦR : ∀ b : ↥Ba, Φ b ∈ Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i}))
    (hΦC : ∀ (c : ↥C) (hc : ((c : ↥C) : K) ∈ Ba), Φ ⟨_, hc⟩ = algebraMap S (Localization.Away (Ψ a)) (Ψ c))
    (hΦJ : ∀ (x : K) (hx : x ∈ Ba) (i : ↥C), i ∈ J → x * ((a : ↥C) : K) = ((i : ↥C) : K) →
      Φ ⟨x, hx⟩ * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) (Ψ i))
    (hret : ∀ k : ℕ, ∃ ρ : ↥(Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i})) →+* (↥Ba ⧸ P ^ k),
      (∀ b : ↥Ba, ρ ⟨Φ b, hΦR b⟩ = Ideal.Quotient.mk (P ^ k) b) ∧
      (∀ (s : S) (hs : algebraMap S (Localization.Away (Ψ a)) s ∈ Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i})) (c : ↥C) (hc : ((c : ↥C) : K) ∈ Ba),
          Ψ c - s ∈ 𝔫 ^ k → ρ ⟨algebraMap S (Localization.Away (Ψ a)) s, hs⟩ = Ideal.Quotient.mk (P ^ k) ⟨_, hc⟩)) :
    ∃ (P' : Ideal ↥(Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i}))) (_ : P'.IsMaximal),
      (∀ b : ↥Ba, (⟨Φ b, hΦR b⟩ : ↥(Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i}))) ∈ P' ↔ b ∈ P) ∧
      (∀ (s : S) (hs : algebraMap S (Localization.Away (Ψ a)) s ∈ Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i})),
        s ∈ 𝔫 → (⟨algebraMap S (Localization.Away (Ψ a)) s, hs⟩ : ↥(Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i}))) ∈ P') ∧
      ∃ T : AdicCompletion P ↥Ba ≃+* AdicCompletion P' ↥(Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i})),
        ∀ b : ↥Ba, T (algebraMap ↥Ba (AdicCompletion P ↥Ba) b) =
          algebraMap ↥(Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i})) (AdicCompletion P' ↥(Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i}))) ⟨Φ b, hΦR b⟩ := by
  classical

  let La := Localization.Away (Ψ a)
  let ιS : S →+* La := algebraMap S La
  let R : Subring La := Subring.closure
      (Set.range (algebraMap S (Localization.Away (Ψ a))) ∪
        {x : Localization.Away (Ψ a) | ∃ i ∈ 𝔐, x * algebraMap S (Localization.Away (Ψ a)) (Ψ a) = algebraMap S (Localization.Away (Ψ a)) i})
  have hSR : ∀ s : S, ιS s ∈ R := fun s => Subring.subset_closure (Or.inl ⟨s, rfl⟩)
  let ιSR : S →+* ↥R := ιS.codRestrict R hSR
  let Φ' : ↥Ba →+* ↥R := Φ.codRestrict R hΦR
  have hCBa : ∀ c : ↥C, ((c : ↥C) : K) ∈ Ba := fun c => by
    rw [hBa, Subalgebra.mem_restrictScalars]; exact Subalgebra.algebraMap_mem _ c

  let P' : Ideal ↥R := Ideal.map Φ' P ⊔ Ideal.map ιSR 𝔫
  have hP'Φ : ∀ b ∈ P, Φ' b ∈ P' := fun b hb => Ideal.mem_sup_left (Ideal.mem_map_of_mem Φ' hb)
  have hP'𝔫 : ∀ s ∈ 𝔫, ιSR s ∈ P' := fun s hs => Ideal.mem_sup_right (Ideal.mem_map_of_mem ιSR hs)
  have hpowΦ : ∀ (k : ℕ) (b : ↥Ba), b ∈ P ^ k → Φ' b ∈ P' ^ k := fun k b hb => by
    have := Ideal.mem_map_of_mem Φ' hb
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (le_sup_left : Ideal.map Φ' P ≤ P') k this
  have hpow𝔫 : ∀ (k : ℕ) (s : S), s ∈ 𝔫 ^ k → ιSR s ∈ P' ^ k := fun k s hs => by
    have := Ideal.mem_map_of_mem ιSR hs
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (le_sup_right : Ideal.map ιSR 𝔫 ≤ P') k this

  have hu : IsUnit (ιS (Ψ a)) := IsLocalization.Away.algebraMap_isUnit (Ψ a)
  have hRgen : ∀ x : La, x ∈ R → x ∈ Subring.closure (Set.range ιS ∪ Set.range Φ) := by
    intro x hx
    refine Subring.closure_le.mpr ?_ hx
    rintro z (⟨s, rfl⟩ | ⟨i, hi, hz⟩)
    · exact Subring.subset_closure (Or.inl ⟨s, rfl⟩)
    ·
      have hz' : z = ιS i * ((hu.unit⁻¹ : Laˣ) : La) := by
        rw [← hz, mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [hz']
      rw [← h𝔐] at hi
      have hi' : i ∈ Submodule.span S (Ψ '' (J : Set ↥C)) := hi
      clear hi hz hz'
      induction hi' using Submodule.span_induction with
      | mem i hi =>
        obtain ⟨j, hj, rfl⟩ := hi

        have hjBa : ((j : ↥C) : K) * (((a : ↥C) : K))⁻¹ ∈ Ba := by
          rw [hBa, Subalgebra.mem_restrictScalars]
          exact Algebra.subset_adjoin ⟨j, hj, by rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]⟩
        have hΦj := hΦJ _ hjBa j hj (by rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one])
        have : ιS (Ψ j) * ((hu.unit⁻¹ : Laˣ) : La) = Φ ⟨_, hjBa⟩ := by
          rw [← hΦj, mul_assoc, IsUnit.mul_val_inv, mul_one]
        rw [this]
        exact Subring.subset_closure (Or.inr ⟨_, rfl⟩)
      | zero => rw [map_zero, zero_mul]; exact Subring.zero_mem _
      | add i₁ i₂ _ _ h₁ h₂ => rw [map_add, add_mul]; exact Subring.add_mem _ h₁ h₂
      | smul s i _ hi' =>
        rw [smul_eq_mul, map_mul, mul_assoc]
        exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨s, rfl⟩)) hi'

  have hle : Subring.closure (Set.range ιS ∪ Set.range Φ) ≤ R := by
    refine Subring.closure_le.mpr ?_
    rintro z (⟨s, rfl⟩ | ⟨b, rfl⟩)
    · exact hSR s
    · exact hΦR b
  have hsurj : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (P' ^ k)).comp Φ') := by
    intro k r
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    suffices h : ∀ (x : La) (hx : x ∈ Subring.closure (Set.range ιS ∪ Set.range Φ)),
        ∃ b : ↥Ba, (⟨x, hle hx⟩ : ↥R) - Φ' b ∈ P' ^ k by
      obtain ⟨b, hb⟩ := h r.1 (hRgen r.1 r.2)
      refine ⟨b, ?_⟩
      rw [RingHom.comp_apply, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact hb
    intro x hx
    induction hx using Subring.closure_induction with
    | mem z hz =>
      rcases hz with ⟨s, rfl⟩ | ⟨b, rfl⟩
      · obtain ⟨c, hc⟩ := hdense k s
        refine ⟨⟨_, hCBa c⟩, ?_⟩
        have : (⟨ιS s, hle (Subring.subset_closure (Or.inl ⟨s, rfl⟩))⟩ : ↥R) - Φ' ⟨_, hCBa c⟩ = ιSR (-(Ψ c - s)) := by
          apply Subtype.ext
          show ιS s - Φ ⟨_, hCBa c⟩ = ιS (-(Ψ c - s))
          rw [hΦC, map_neg, map_sub, neg_sub]
        rw [this]
        exact hpow𝔫 k _ (Submodule.neg_mem _ hc)
      · exact ⟨b, by rw [show (⟨Φ b, hle (Subring.subset_closure (Or.inr ⟨b, rfl⟩))⟩ : ↥R) = Φ' b from rfl, sub_self]; exact Ideal.zero_mem _⟩
    | zero => exact ⟨0, by rw [map_zero, sub_zero, show (⟨(0 : La), hle (Subring.zero_mem _)⟩ : ↥R) = 0 from rfl]; exact Ideal.zero_mem _⟩
    | one => exact ⟨1, by rw [map_one, show (⟨(1 : La), hle (Subring.one_mem _)⟩ : ↥R) = 1 from rfl, sub_self]; exact Ideal.zero_mem _⟩
    | add x z hx' hz' ihx ihz =>
      obtain ⟨b₁, h₁⟩ := ihx
      obtain ⟨b₂, h₂⟩ := ihz
      refine ⟨b₁ + b₂, ?_⟩
      have e : (⟨x + z, hle (Subring.add_mem _ hx' hz')⟩ : ↥R) - Φ' (b₁ + b₂) =
          ((⟨x, hle hx'⟩ : ↥R) - Φ' b₁) + ((⟨z, hle hz'⟩ : ↥R) - Φ' b₂) := by
        rw [map_add, show (⟨x + z, hle (Subring.add_mem _ hx' hz')⟩ : ↥R) = ⟨x, hle hx'⟩ + ⟨z, hle hz'⟩ from rfl]
        abel
      rw [e]; exact Ideal.add_mem _ h₁ h₂
    | neg x hx' ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨-b, ?_⟩
      have e : (⟨-x, hle (Subring.neg_mem _ hx')⟩ : ↥R) - Φ' (-b) = -((⟨x, hle hx'⟩ : ↥R) - Φ' b) := by
        rw [map_neg, show (⟨-x, hle (Subring.neg_mem _ hx')⟩ : ↥R) = -⟨x, hle hx'⟩ from rfl]
        abel
      rw [e]; exact Submodule.neg_mem _ hb
    | mul x z hx' hz' ihx ihz =>
      obtain ⟨b₁, h₁⟩ := ihx
      obtain ⟨b₂, h₂⟩ := ihz
      refine ⟨b₁ * b₂, ?_⟩
      have e : (⟨x * z, hle (Subring.mul_mem _ hx' hz')⟩ : ↥R) - Φ' (b₁ * b₂) =
          ((⟨x, hle hx'⟩ : ↥R) - Φ' b₁) * ⟨z, hle hz'⟩ + Φ' b₁ * ((⟨z, hle hz'⟩ : ↥R) - Φ' b₂) := by
        rw [map_mul, show (⟨x * z, hle (Subring.mul_mem _ hx' hz')⟩ : ↥R) = ⟨x, hle hx'⟩ * ⟨z, hle hz'⟩ from rfl]
        ring
      rw [e]; exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h₁) (Ideal.mul_mem_left _ _ h₂)

  have hker : ∀ k : ℕ, RingHom.ker ((Ideal.Quotient.mk (P' ^ k)).comp Φ') = P ^ k := by
    intro k
    refine le_antisymm ?_ (fun b hb => by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]; exact hpowΦ k b hb)
    intro b hb
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hb
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    obtain ⟨ρ, hρΦ, hρS⟩ := hret k

    have hρP' : Ideal.map ρ P' ≤ Ideal.map (Ideal.Quotient.mk (P ^ k)) P := by
      rw [Ideal.map_sup, Ideal.map_map, Ideal.map_map, sup_le_iff]
      constructor
      · rw [Ideal.map_le_iff_le_comap]
        intro p hp
        rw [Ideal.mem_comap, RingHom.comp_apply, show ρ (Φ' p) = Ideal.Quotient.mk (P ^ k) p from hρΦ p]
        exact Ideal.mem_map_of_mem _ hp
      · rw [Ideal.map_le_iff_le_comap]
        intro s hs
        obtain ⟨c, hc⟩ := hdense k s
        rw [Ideal.mem_comap, RingHom.comp_apply, show ρ (ιSR s) = Ideal.Quotient.mk (P ^ k) ⟨_, hCBa c⟩ from hρS s (hSR s) c (hCBa c) hc]
        refine Ideal.mem_map_of_mem _ ((hPy c (hCBa c)).mpr ?_)

        have h1 : Ψ c ∈ 𝔫 := by
          have := Ideal.add_mem _ (Ideal.pow_le_self hk.ne' hc) hs
          rwa [sub_add_cancel] at this
        have h2 : c ∈ Ideal.comap Ψ (𝔫 ^ 1) := by rw [pow_one]; exact h1
        rw [hcomap 1, pow_one] at h2
        exact h2
    have hρb : ρ (Φ' b) ∈ Ideal.map ρ (P' ^ k) := Ideal.mem_map_of_mem ρ hb
    rw [Ideal.map_pow] at hρb
    have hbot : (Ideal.map (Ideal.Quotient.mk (P ^ k)) P) ^ k = ⊥ := by
      rw [← Ideal.map_pow, Ideal.map_quotient_self]
    have h0 : ρ (Φ' b) = 0 := by
      have := Ideal.pow_right_mono hρP' k hρb
      rwa [hbot, Ideal.mem_bot] at this
    rw [show ρ (Φ' b) = Ideal.Quotient.mk (P ^ k) b from hρΦ b, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0

  obtain ⟨T, hT⟩ := AdicCompletion.exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow P P' Φ' hsurj hker
  have h1 : Function.Surjective ((Ideal.Quotient.mk P').comp Φ') := by
    intro r
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨b, hb⟩ := hsurj 1 (Ideal.Quotient.mk (P' ^ 1) r')
    refine ⟨b, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hb ⊢
    rwa [pow_one] at hb
  have hk1 : RingHom.ker ((Ideal.Quotient.mk P').comp Φ') = P := by
    ext b
    have := SetLike.ext_iff.mp (hker 1) b
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, pow_one, pow_one] at this
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact this
  have hmem : ∀ b : ↥Ba, Φ' b ∈ P' ↔ b ∈ P := fun b => by
    have := SetLike.ext_iff.mp hk1 b
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have hmax : P'.IsMaximal := by
    have hfield : IsField (↥Ba ⧸ RingHom.ker ((Ideal.Quotient.mk P').comp Φ')) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (hk1.symm ▸ hP)
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient P').mpr
      (MulEquiv.isField hfield (RingHom.quotientKerEquivOfSurjective h1).toMulEquiv.symm)
  exact ⟨P', hmax, hmem, fun s hs hsn => hP'𝔫 s hsn, T, hT⟩

set_option maxHeartbeats 3200000 in

theorem BCLG.sigma
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (C : Subalgebra A K) (y : Ideal ↥C) (J : Ideal ↥C)
    (a : ↥C)
    (Ba : Subalgebra A K)
    (hBa : Ba = (Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A)
    (P : Ideal ↥Ba)
    (hPy : ∀ (b : ↥C) (hb : ((b : ↥C) : K) ∈ Ba), (⟨_, hb⟩ : ↥Ba) ∈ P ↔ b ∈ y)
    (S : Type*) [CommRing S] (Ψ : ↥C →+* S)
    (𝔫 : Ideal S)
    (hdense : ∀ (n : ℕ) (s : S), ∃ c : ↥C, Ψ c - s ∈ 𝔫 ^ n)
    (hcomap : ∀ n : ℕ, Ideal.comap Ψ (𝔫 ^ n) = y ^ n) (k : ℕ) :
    ∃ σ : S →+* (↥Ba ⧸ P ^ k), ∀ (s : S) (c : ↥C) (hc : ((c : ↥C) : K) ∈ Ba),
      Ψ c - s ∈ 𝔫 ^ k → σ s = Ideal.Quotient.mk (P ^ k) ⟨_, hc⟩ := by
  classical
  have hCBa : ∀ c : ↥C, ((c : ↥C) : K) ∈ Ba := fun c => by
    rw [hBa, Subalgebra.mem_restrictScalars]; exact Subalgebra.algebraMap_mem _ c
  let ιCBa : ↥C →+* ↥Ba :=
    { toFun := fun c => ⟨(c : K), hCBa c⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hyP : y ^ k ≤ Ideal.comap ιCBa (P ^ k) := by
    refine le_trans (Ideal.pow_right_mono ?_ k) (Ideal.le_comap_pow _ k)
    intro c hc
    exact (hPy c (hCBa c)).mpr hc
  let q : ↥C ⧸ y ^ k →+* ↥Ba ⧸ P ^ k := Ideal.quotientMap (P ^ k) ιCBa hyP
  let e₀ : ↥C ⧸ y ^ k →+* S ⧸ 𝔫 ^ k := Ideal.quotientMap (𝔫 ^ k) Ψ (hcomap k).ge
  have he₀inj : Function.Injective e₀ := Ideal.quotientMap_injective' (hcomap k).le
  have he₀surj : Function.Surjective e₀ := by
    intro t
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨c, hc⟩ := hdense k s
    exact ⟨Ideal.Quotient.mk _ c, by rw [Ideal.quotientMap_mk]; exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hc⟩
  let e := RingEquiv.ofBijective e₀ ⟨he₀inj, he₀surj⟩
  refine ⟨(q.comp e.symm.toRingHom).comp (Ideal.Quotient.mk (𝔫 ^ k)), fun s c hc hcs => ?_⟩
  have h1 : Ideal.Quotient.mk (𝔫 ^ k) s = e (Ideal.Quotient.mk (y ^ k) c) := by
    rw [RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]
    exact ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hcs).symm
  show q (e.symm (Ideal.Quotient.mk (𝔫 ^ k) s)) = _
  rw [h1, RingEquiv.symm_apply_apply]
  show Ideal.quotientMap (P ^ k) ιCBa hyP (Ideal.Quotient.mk (y ^ k) c) = _
  rw [Ideal.quotientMap_mk]
  rfl

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (C : Subalgebra A K) (y : Ideal ↥C) (hy : y.IsMaximal) (J : Ideal ↥C)
    (a : ↥C) (haJ : a ∈ J) (ha0 : ((a : ↥C) : K) ≠ 0)
    (Ba : Subalgebra A K)
    (hBa : Ba = (Algebra.adjoin ↥C {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)}).restrictScalars A)
    (P : Ideal ↥Ba) (hP : P.IsMaximal)
    (hPy : ∀ (b : ↥C) (hb : ((b : ↥C) : K) ∈ Ba), (⟨_, hb⟩ : ↥Ba) ∈ P ↔ b ∈ y)
    (S : Type*) [CommRing S] (Ψ : ↥C →+* S)
    (hflat : letI : Algebra ↥C S := Ψ.toAlgebra; Module.Flat ↥C S)
    (𝔫 : Ideal S) (h𝔫 : Ideal.map Ψ y = 𝔫)
    (hdense : ∀ (n : ℕ) (s : S), ∃ c : ↥C, Ψ c - s ∈ 𝔫 ^ n)
    (hcomap : ∀ n : ℕ, Ideal.comap Ψ (𝔫 ^ n) = y ^ n)
    (𝔐 : Ideal S) (h𝔐 : Ideal.map Ψ J = 𝔐) :
    let La := Localization.Away (Ψ a)
    let R : Subring La := Subring.closure
      (Set.range (algebraMap S La) ∪ {x : La | ∃ i ∈ 𝔐, x * algebraMap S La (Ψ a) = algebraMap S La i})
    Ψ a ∈ nonZeroDivisors S ∧ Ψ a ∈ 𝔐 ∧
    ∃ (Φ : ↥Ba →+* La) (hΦR : ∀ b : ↥Ba, Φ b ∈ R),
      (∀ (c : ↥C) (hc : ((c : ↥C) : K) ∈ Ba), Φ ⟨_, hc⟩ = algebraMap S La (Ψ c)) ∧
      (∀ (x : K) (hx : x ∈ Ba) (i : ↥C), i ∈ J → x * ((a : ↥C) : K) = ((i : ↥C) : K) →
        Φ ⟨x, hx⟩ * algebraMap S La (Ψ a) = algebraMap S La (Ψ i)) ∧
      ∃ (P' : Ideal ↥R) (_ : P'.IsMaximal),
        (∀ b : ↥Ba, (⟨Φ b, hΦR b⟩ : ↥R) ∈ P' ↔ b ∈ P) ∧
        (∀ (s : S) (hs : algebraMap S La s ∈ R), s ∈ 𝔫 → (⟨algebraMap S La s, hs⟩ : ↥R) ∈ P') ∧
        ∃ T : AdicCompletion P ↥Ba ≃+* AdicCompletion P' ↥R,
          ∀ b : ↥Ba, T (algebraMap ↥Ba (AdicCompletion P ↥Ba) b) =
            algebraMap ↥R (AdicCompletion P' ↥R) ⟨Φ b, hΦR b⟩ := by
  intro La R
  classical
  letI algCS : Algebra ↥C S := Ψ.toAlgebra
  haveI : Module.Flat ↥C S := hflat
  have hΨalg : ∀ c : ↥C, algebraMap ↥C S c = Ψ c := fun _ => rfl

  have ha0' : (a : ↥C) ≠ 0 := fun h => ha0 (by rw [h]; rfl)
  have hregC : IsSMulRegular ↥C (a : ↥C) := fun x y h => mul_left_cancel₀ ha0' (by simpa [smul_eq_mul] using h)
  have hnzd : Ψ a ∈ nonZeroDivisors S := by
    have hreg : IsSMulRegular S (algebraMap ↥C S a) := hregC.of_flat
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    refine hreg ?_
    show algebraMap ↥C S a • x = algebraMap ↥C S a • (0 : S)
    rw [smul_eq_mul, smul_eq_mul, mul_zero, hΨalg, mul_comm, hx]
  have haM : Ψ a ∈ 𝔐 := h𝔐 ▸ Ideal.mem_map_of_mem Ψ haJ
  refine ⟨hnzd, haM, ?_⟩

  let S₀ := Localization.Away (a : ↥C)
  have hunitK : IsUnit (algebraMap ↥C K a) := isUnit_iff_ne_zero.mpr ha0
  let j₀ : S₀ →ₐ[↥C] K :=
    { IsLocalization.Away.lift (a : ↥C) hunitK with
      commutes' := fun c => IsLocalization.Away.lift_eq (a : ↥C) hunitK c }
  have hj₀c : ∀ c : ↥C, j₀ (algebraMap ↥C S₀ c) = (c : K) := fun c => IsLocalization.Away.lift_eq (a : ↥C) hunitK c
  have hinjC : Function.Injective (algebraMap ↥C S₀) :=
    IsLocalization.injective S₀ (powers_le_nonZeroDivisors_of_noZeroDivisors ha0')
  have hj₀inj : Function.Injective j₀ := by
    have key := (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (a : ↥C)) (j₀ : S₀ →+* K)).mpr
      (fun x y => by
        constructor
        · intro h; rw [h]
        · intro h
          have h' : (x : K) = (y : K) := by
            have hx := hj₀c x; have hy := hj₀c y
            rw [← hx, ← hy]; exact h
          rw [Subtype.ext h'])
    exact key
  let B : Subalgebra ↥C S₀ :=
    Algebra.adjoin ↥C {x : S₀ | ∃ i ∈ J, x * algebraMap ↥C S₀ a = algebraMap ↥C S₀ i}

  have himg : (j₀ : S₀ → K) '' {x : S₀ | ∃ i ∈ J, x * algebraMap ↥C S₀ a = algebraMap ↥C S₀ i} =
      {x : K | ∃ i ∈ J, x * ((a : ↥C) : K) = ((i : ↥C) : K)} := by
    ext x
    constructor
    · rintro ⟨x₀, ⟨i, hi, hx₀⟩, rfl⟩
      refine ⟨i, hi, ?_⟩
      have := congrArg j₀ hx₀
      rwa [map_mul, hj₀c, hj₀c] at this
    · rintro ⟨i, hi, hx⟩
      refine ⟨IsLocalization.mk' S₀ i ⟨a, Submonoid.mem_powers _⟩, ⟨i, hi, ?_⟩, ?_⟩
      · exact IsLocalization.mk'_spec S₀ i ⟨a, Submonoid.mem_powers _⟩
      · have hxa : x = ((i : ↥C) : K) * (((a : ↥C) : K))⁻¹ := by
          rw [← hx, mul_assoc, mul_inv_cancel₀ ha0, mul_one]
        rw [hxa]
        have hs := congrArg j₀ (IsLocalization.mk'_spec S₀ i ⟨a, Submonoid.mem_powers _⟩)
        rw [map_mul] at hs
        have ha' : j₀ (algebraMap ↥C S₀ ((⟨a, Submonoid.mem_powers _⟩ : Submonoid.powers (a : ↥C)) : ↥C)) = (a : K) := hj₀c a
        rw [ha', hj₀c] at hs
        exact (eq_mul_inv_iff_mul_eq₀ ha0).mpr hs
  have hBa' : ∀ x : K, x ∈ Ba ↔ x ∈ B.map j₀ := by
    intro x
    rw [hBa, Subalgebra.mem_restrictScalars, AlgHom.map_adjoin, himg]

  let e₀ : ↥B ≃ₐ[↥C] ↥(B.map j₀) := B.equivMapOfInjective j₀ hj₀inj
  let incl : ↥Ba →+* ↥(B.map j₀) :=
    { toFun := fun b => ⟨(b : K), (hBa' b).mp b.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let pre : ↥Ba →+* S₀ := (B.val.toRingHom.comp (e₀.symm : ↥(B.map j₀) ≃ₐ[↥C] ↥B).toRingHom).comp incl
  have hpre : ∀ b : ↥Ba, j₀ (pre b) = (b : K) := by
    intro b
    show j₀ ((e₀.symm (incl b) : ↥B) : S₀) = (b : K)
    have := Subalgebra.coe_equivMapOfInjective_apply B j₀ hj₀inj (e₀.symm (incl b))
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm
  have hpreC : ∀ (c : ↥C) (hc : ((c : ↥C) : K) ∈ Ba), pre ⟨_, hc⟩ = algebraMap ↥C S₀ c := by
    intro c hc
    apply hj₀inj
    rw [hpre, hj₀c]

  have hCLa : ∀ c : ↥C, algebraMap ↥C La c = algebraMap S La (Ψ c) := fun c =>
    (IsScalarTower.algebraMap_apply ↥C S La c)
  haveI : IsLocalization.Away (algebraMap ↥C S a) La := by
    show IsLocalization.Away (Ψ a) La; infer_instance
  have hunitLa : IsUnit (algebraMap ↥C La a) := by
    rw [hCLa]; exact IsLocalization.Away.algebraMap_isUnit (Ψ a)
  let φ : S₀ →ₐ[↥C] La :=
    { IsLocalization.Away.lift (a : ↥C) hunitLa with
      commutes' := fun c => IsLocalization.Away.lift_eq (a : ↥C) hunitLa c }
  have hφc : ∀ c : ↥C, φ (algebraMap ↥C S₀ c) = algebraMap S La (Ψ c) := fun c => by
    rw [← hCLa]; exact IsLocalization.Away.lift_eq (a : ↥C) hunitLa c

  let Φ : ↥Ba →+* La := φ.toRingHom.comp pre
  have hΦpre : ∀ b : ↥Ba, Φ b = φ (pre b) := fun _ => rfl

  let Rsub : Subalgebra S La := Algebra.adjoin S {x : La | ∃ i ∈ 𝔐, x * algebraMap S La (Ψ a) = algebraMap S La i}
  have hRiff : ∀ x : La, x ∈ R ↔ x ∈ Rsub := fun x => by
    show x ∈ R ↔ x ∈ Algebra.adjoin S _; rw [Algebra.mem_adjoin_iff]
  have hBle : B ≤ (Rsub.restrictScalars ↥C).comap φ := by
    refine Algebra.adjoin_le ?_
    rintro x₀ ⟨i, hi, hx₀⟩
    show φ x₀ ∈ Rsub
    refine Algebra.subset_adjoin ⟨Ψ i, h𝔐 ▸ Ideal.mem_map_of_mem Ψ hi, ?_⟩
    have := congrArg φ hx₀
    rwa [map_mul, hφc, hφc] at this
  have hΦR : ∀ b : ↥Ba, Φ b ∈ R := by
    intro b
    rw [hRiff, hΦpre]
    have : (pre b) ∈ B := by
      show ((e₀.symm (incl b) : ↥B) : S₀) ∈ B
      exact (e₀.symm (incl b)).2
    exact hBle this
  have hΦC : ∀ (c : ↥C) (hc : ((c : ↥C) : K) ∈ Ba), Φ ⟨_, hc⟩ = algebraMap S La (Ψ c) := by
    intro c hc
    rw [hΦpre, hpreC c hc, hφc]
  have hΦJ : ∀ (x : K) (hx : x ∈ Ba) (i : ↥C), i ∈ J → x * ((a : ↥C) : K) = ((i : ↥C) : K) →
      Φ ⟨x, hx⟩ * algebraMap S La (Ψ a) = algebraMap S La (Ψ i) := by
    intro x hx i hiJ hxi
    rw [hΦpre, ← hφc, ← hφc, ← map_mul]
    congr 1
    apply hj₀inj
    rw [map_mul, hpre, hj₀c, hj₀c]
    exact hxi
  have hCBa : ∀ c : ↥C, ((c : ↥C) : K) ∈ Ba := fun c => by
    rw [hBa', ← hj₀c]; exact ⟨algebraMap ↥C S₀ c, B.algebraMap_mem c, rfl⟩
  let inclC : ↥C →+* ↥Ba :=
    { toFun := fun c => ⟨(c : K), hCBa c⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let inclInv : ↥(B.map j₀) →+* ↥Ba :=
    { toFun := fun x => ⟨(x : K), (hBa' x).mpr x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hinclInv : ∀ b : ↥Ba, inclInv (incl b) = b := fun b => Subtype.ext rfl

  obtain ⟨hθinj, hθrange⟩ := Algebra.adjoin_div_tensorProduct_bijective_of_flat (C' := S) J (a : ↥C) S₀ La φ
  let θ : S ⊗[↥C] ↥B →ₐ[S] La :=
    Algebra.TensorProduct.lift (Algebra.ofId S La) (φ.comp B.val) (fun _ _ => Commute.all _ _)
  have hgenEq : {x : La | ∃ i ∈ Ideal.map (algebraMap ↥C S) J,
        x * algebraMap S La (algebraMap ↥C S a) = algebraMap S La i} =
      {x : La | ∃ i ∈ 𝔐, x * algebraMap S La (Ψ a) = algebraMap S La i} := by
    rw [show Ideal.map (algebraMap ↥C S) J = 𝔐 from h𝔐]; rfl
  have hθmem : ∀ z : S ⊗[↥C] ↥B, θ z ∈ R := by
    intro z
    rw [hRiff]
    have := (hθrange (θ z)).mp ⟨z, rfl⟩
    show θ z ∈ Algebra.adjoin S _
    rwa [hgenEq] at this
  have hθsurj : ∀ r : La, r ∈ R → ∃ z, θ z = r := by
    intro r hr
    rw [hRiff] at hr
    have : r ∈ Algebra.adjoin S {x : La | ∃ i ∈ Ideal.map (algebraMap ↥C S) J,
        x * algebraMap S La (algebraMap ↥C S a) = algebraMap S La i} := by rwa [hgenEq]
    exact (hθrange r).mpr this
  let θR : S ⊗[↥C] ↥B →+* ↥R := θ.toRingHom.codRestrict R hθmem
  have hθRbij : Function.Bijective θR := by
    constructor
    · intro z₁ z₂ h; exact hθinj (congrArg Subtype.val h)
    · intro r; obtain ⟨z, hz⟩ := hθsurj r.1 r.2; exact ⟨z, Subtype.ext hz⟩
  let eθ : S ⊗[↥C] ↥B ≃+* ↥R := RingEquiv.ofBijective θR hθRbij
  have heθΦ : ∀ b : ↥Ba, eθ ((1 : S) ⊗ₜ[↥C] (e₀.symm (incl b) : ↥B)) = ⟨Φ b, hΦR b⟩ := by
    intro b
    apply Subtype.ext
    rw [RingEquiv.ofBijective_apply]
    show θ ((1 : S) ⊗ₜ[↥C] (e₀.symm (incl b) : ↥B)) = Φ b
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  have heθS : ∀ (s : S) (hs : algebraMap S La s ∈ R), eθ (s ⊗ₜ[↥C] (1 : ↥B)) = ⟨algebraMap S La s, hs⟩ := by
    intro s hs
    apply Subtype.ext
    rw [RingEquiv.ofBijective_apply]
    show θ (s ⊗ₜ[↥C] (1 : ↥B)) = algebraMap S La s
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have hret : ∀ k : ℕ, ∃ ρ : ↥R →+* (↥Ba ⧸ P ^ k),
      (∀ b : ↥Ba, ρ ⟨Φ b, hΦR b⟩ = Ideal.Quotient.mk (P ^ k) b) ∧
      (∀ (s : S) (hs : algebraMap S La s ∈ R) (c : ↥C) (hc : ((c : ↥C) : K) ∈ Ba),
          Ψ c - s ∈ 𝔫 ^ k → ρ ⟨algebraMap S La s, hs⟩ = Ideal.Quotient.mk (P ^ k) ⟨_, hc⟩) := by
    intro k
    obtain ⟨σ, hσ⟩ := BCLG.sigma C y J a Ba hBa P hPy S Ψ 𝔫 hdense hcomap k
    letI algCBa : Algebra ↥C ↥Ba := inclC.toAlgebra
    have halgBa : ∀ c : ↥C, algebraMap ↥C ↥Ba c = ⟨(c : K), hCBa c⟩ := fun _ => rfl
    let σₐ : S →ₐ[↥C] (↥Ba ⧸ P ^ k) :=
      { σ with
        commutes' := fun c => by
          show σ (algebraMap ↥C S c) = algebraMap ↥C (↥Ba ⧸ P ^ k) c
          rw [IsScalarTower.algebraMap_apply ↥C ↥Ba (↥Ba ⧸ P ^ k) c, Ideal.Quotient.algebraMap_eq, halgBa, hΨalg]
          exact hσ (Ψ c) c (hCBa c) (by rw [sub_self]; exact Ideal.zero_mem _) }
    let βr : ↥B →+* (↥Ba ⧸ P ^ k) :=
      (Ideal.Quotient.mk (P ^ k)).comp (inclInv.comp (e₀ : ↥B ≃ₐ[↥C] ↥(B.map j₀)).toRingHom)
    let βₐ : ↥B →ₐ[↥C] (↥Ba ⧸ P ^ k) :=
      { βr with
        commutes' := fun c => by
          show Ideal.Quotient.mk (P ^ k) (inclInv (e₀ (algebraMap ↥C ↥B c))) = algebraMap ↥C (↥Ba ⧸ P ^ k) c
          rw [IsScalarTower.algebraMap_apply ↥C ↥Ba (↥Ba ⧸ P ^ k) c, Ideal.Quotient.algebraMap_eq, halgBa]
          congr 1
          apply Subtype.ext
          show ((e₀ (algebraMap ↥C ↥B c) : ↥(B.map j₀)) : K) = (c : K)
          rw [Subalgebra.coe_equivMapOfInjective_apply]
          exact hj₀c c }
    let τ : S ⊗[↥C] ↥B →ₐ[↥C] (↥Ba ⧸ P ^ k) := Algebra.TensorProduct.lift σₐ βₐ (fun _ _ => Commute.all _ _)
    refine ⟨τ.toRingHom.comp eθ.symm.toRingHom, ?_, ?_⟩
    · intro b
      show τ (eθ.symm ⟨Φ b, hΦR b⟩) = _
      rw [← heθΦ b, RingEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      show Ideal.Quotient.mk (P ^ k) (inclInv (e₀ (e₀.symm (incl b)))) = _
      rw [AlgEquiv.apply_symm_apply, hinclInv]
    · intro s hs c hc hsc
      show τ (eθ.symm ⟨algebraMap S La s, hs⟩) = _
      rw [← heθS s hs, RingEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact hσ s c hc hsc
  obtain ⟨P', hP'max, h1, h2, T, hT⟩ :=
    BCLG.levelwise C y hy J a haJ ha0 Ba hBa P hP hPy S Ψ hflat 𝔫 h𝔫 hdense hcomap 𝔐 h𝔐 Φ hΦR hΦC hΦJ hret
  exact ⟨Φ, hΦR, hΦC, hΦJ, P', hP'max, h1, h2, T, hT⟩

end S_Subalgebra_exists_ringHom_ringEquiv_adicCompletion_adjoin_div_of_flat_of_dense
end P2MW
export P2MW.S_Subalgebra_exists_ringHom_ringEquiv_adicCompletion_adjoin_div_of_flat_of_dense (solution)
