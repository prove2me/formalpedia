-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P21.band_irreducible_classification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:29:11.225018+00:00
-- url     : https://prove2.me/submissions/381bcdba-7ad5-4af8-adb9-9f15f7fa2173

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P21

namespace QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

section X7T

variable {S : Type v} [Semigroup S]

theorem X7T_idem_withOne (hband : ∀ s : S, s * s = s) (x : WithOne S) : x * x = x := by
  cases x with
  | one => simp
  | coe a => rw [← WithOne.coe_mul, hband a]

theorem X7T_mem_self (s : S) : s ∈ principalIdeal s := ⟨1, 1, by simp⟩

theorem X7T_trans {x y z : S} (hxy : x ∈ principalIdeal y) (hyz : y ∈ principalIdeal z) :
    x ∈ principalIdeal z := by
  obtain ⟨a, b, hab⟩ := hxy
  obtain ⟨c, d, hcd⟩ := hyz
  refine ⟨a * c, d * b, ?_⟩
  rw [hab, hcd]
  simp only [mul_assoc]

/-- In a band, `e ≤_J s` iff `e s e = e`. -/
theorem X7T_mem_iff (hband : ∀ s : S, s * s = s) (e s : S) :
    e ∈ principalIdeal s ↔ e * s * e = e := by
  constructor
  · rintro ⟨a, b, hE⟩
    have hid := X7T_idem_withOne hband
    apply WithOne.coe_injective
    simp only [WithOne.coe_mul]
    set E : WithOne S := (e : WithOne S)
    set T : WithOne S := (s : WithOne S)
    have h1 : E * T * b = E := by
      calc E * T * b = a * ((T * b) * (T * b)) := by rw [hE]; simp only [mul_assoc]
        _ = E := by rw [hid, hE, mul_assoc]
    calc E * T * E = (E * T) * (E * T * b) := by rw [h1]
      _ = ((E * T) * (E * T)) * b := by simp only [mul_assoc]
      _ = E := by rw [hid, h1]
  · intro h
    exact ⟨(e : WithOne S), (e : WithOne S), by rw [← WithOne.coe_mul, ← WithOne.coe_mul, h]⟩

theorem X7T_mul (e s t : S) (hband : ∀ s : S, s * s = s) (hse : e * s * e = e)
    (hte : e * t * e = e) : e * (s * t) * e = e := by
  have h1 : e * (t * e * s) * e = e := by
    calc e * (t * e * s) * e = (e * t * e) * (s * e) := by simp only [mul_assoc]
      _ = e := by rw [hte, ← mul_assoc, hse]
  have h2 := hband (t * e * s)
  calc e * (s * t) * e = (e * t * e) * (s * t) * (e * s * e) := by rw [hte, hse]
    _ = e * ((t * e * s) * (t * e * s)) * e := by simp only [mul_assoc]
    _ = e := by rw [h2, h1]

theorem X7T_mul_left (hband : ∀ s : S, s * s = s) (e s t : S)
    (h : e * (s * t) * e = e) : e * s * e = e := by
  rw [← X7T_mem_iff hband]
  exact ⟨(e : WithOne S), ((t * e : S) : WithOne S), by
    rw [← WithOne.coe_mul, ← WithOne.coe_mul]; congr 1; simpa only [mul_assoc] using h.symm⟩

theorem X7T_mul_right (hband : ∀ s : S, s * s = s) (e s t : S)
    (h : e * (s * t) * e = e) : e * t * e = e := by
  rw [← X7T_mem_iff hband]
  exact ⟨((e * s : S) : WithOne S), (e : WithOne S), by
    rw [← WithOne.coe_mul, ← WithOne.coe_mul]; congr 1; simpa only [mul_assoc] using h.symm⟩

theorem X7T_mem_classIdeal (hband : ∀ s : S, s * s = s) (J : JClass S) (g : S)
    (hg : J.val = greenClass g) (s : S) : s ∈ classIdeal J ↔ g * s * g ≠ g := by
  rw [ne_eq, ← X7T_mem_iff hband]
  simp only [classIdeal, Set.mem_ofPred_eq, hg]
  constructor
  · intro h hg'
    apply h
    intro t ht
    have : t ∈ principalIdeal g := by
      have ht' : principalIdeal t = principalIdeal g := ht
      rw [← ht']; exact X7T_mem_self t
    exact X7T_trans this hg'
  · intro h hsub
    exact h (hsub (show principalIdeal g = principalIdeal g from rfl))

theorem X7T_sc_one {K : Type u} [CommRing K] (hband : ∀ s : S, s * s = s) (J : JClass S) (g : S)
    (hg : J.val = greenClass g) (s : S) (h : g * s * g = g) : scalarCharacter K J s = 1 := by
  have : s ∉ classIdeal J := by rw [X7T_mem_classIdeal hband J g hg]; simpa using h
  simp [scalarCharacter, this]

theorem X7T_sc_zero {K : Type u} [CommRing K] (hband : ∀ s : S, s * s = s) (J : JClass S) (g : S)
    (hg : J.val = greenClass g) (s : S) (h : g * s * g ≠ g) : scalarCharacter K J s = 0 := by
  have : s ∈ classIdeal J := by rw [X7T_mem_classIdeal hband J g hg]; exact h
  simp [scalarCharacter, this]

end X7T

end QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

open QAlgorithms.Papers.Independent.Renew46.P21 in
theorem solution {K : Type u} {S : Type v}
    [Field K] [Semigroup S] [Finite S] (hband : ∀ s : S, s * s = s) :
    (∀ J : JClass S, ∃ rho : RightSemigroupAction K S K,
      (∀ (s : S) (k : K), rho.act s k = scalarCharacter K J s * k) ∧
      SemigroupSimple rho ∧ HasApex rho J) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module K M]
      (rho : RightSemigroupAction K S M), SemigroupSimple rho →
      FiniteDimensional K M ∧ Module.finrank K M = 1 ∧
        ∃! J : JClass S, HasApex rho J ∧ ScalarModel rho J) := by
  constructor
  · -- existence of the scalar models
    intro J
    obtain ⟨g, hg⟩ := J.property
    have hmul : ∀ s t : S, scalarCharacter K J (s * t) =
        scalarCharacter K J t * scalarCharacter K J s := by
      intro s t
      by_cases hs : g * s * g = g
      · by_cases ht : g * t * g = g
        · rw [X7T_sc_one hband J g hg _ (X7T_mul g s t hband hs ht),
            X7T_sc_one hband J g hg _ hs, X7T_sc_one hband J g hg _ ht, one_mul]
        · rw [X7T_sc_zero hband J g hg _ (fun h => ht (X7T_mul_right hband g s t h)),
            X7T_sc_zero hband J g hg _ ht, zero_mul]
      · rw [X7T_sc_zero hband J g hg _ (fun h => hs (X7T_mul_left hband g s t h)),
          X7T_sc_zero hband J g hg _ hs, mul_zero]
    let rho : RightSemigroupAction K S K :=
      { act := fun s => scalarCharacter K J s • LinearMap.id
        mul_apply := by
          intro s t m
          simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
          rw [hmul]; ring }
    have hact : ∀ (s : S) (k : K), rho.act s k = scalarCharacter K J s * k := by
      intro s k; simp [rho]
    have hgg : g * g * g = g := by rw [hband g, hband g]
    refine ⟨rho, hact, ⟨⟨g, 1, ?_⟩, fun U _ => Ideal.eq_bot_or_top U⟩, ?_, ?_⟩
    · rw [hact, X7T_sc_one hband J g hg _ hgg]; simp
    · exact ⟨g, by rw [hg]; exact (rfl : principalIdeal g = principalIdeal g), hband g⟩
    · ext s
      simp only [semigroupAnnihilator, Set.mem_ofPred_eq]
      simp only [hact]
      rw [X7T_mem_classIdeal hband J g hg]
      constructor
      · intro h hs
        have := h 1
        rw [X7T_sc_one hband J g hg _ hs] at this
        simp at this
      · intro hs m
        rw [X7T_sc_zero hband J g hg _ hs, zero_mul]
  · intro M _ _ rho hsimple
    obtain ⟨⟨s0, m0, hs0⟩, hirr⟩ := hsimple
    set A := rho.act with hA
    have hmulA : ∀ (s t : S) (m : M), A (s * t) m = A t (A s m) := rho.mul_apply
    -- choose a non-annihilating element with minimal principal ideal
    have hex : ∃ n : ℕ, ∃ s : S, A s ≠ 0 ∧ (principalIdeal s).ncard = n :=
      ⟨_, s0, fun h => hs0 (by rw [h]; rfl), rfl⟩
    classical
    obtain ⟨e, he0, hen⟩ := Nat.find_spec hex
    have hmin : ∀ s : S, A s ≠ 0 → Nat.find hex ≤ (principalIdeal s).ncard :=
      fun s hs => Nat.find_min' hex ⟨s, hs, rfl⟩
    -- dichotomy
    have hdich : ∀ s : S, A (e * s * e) = 0 ∨ e * s * e = e := by
      intro s
      by_cases h : A (e * s * e) = 0
      · exact Or.inl h
      · right
        have hsub : principalIdeal (e * s * e) ⊆ principalIdeal e := by
          intro x hx
          exact X7T_trans hx ⟨1, ((s * e : S) : WithOne S), by
            rw [one_mul, ← WithOne.coe_mul, mul_assoc]⟩
        have heq : principalIdeal (e * s * e) = principalIdeal e :=
          Set.eq_of_subset_of_ncard_le hsub (by rw [hen]; exact hmin _ h)
        have hmem : e ∈ principalIdeal (e * s * e) := by rw [heq]; exact X7T_mem_self e
        rw [X7T_mem_iff hband] at hmem
        calc e * s * e = e * (e * s * e) * e := by
              simp only [← mul_assoc, hband e]
              rw [mul_assoc (e * s) e e, hband e]
          _ = e := hmem
    obtain ⟨m1, hm1⟩ : ∃ m, A e m ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact he0 (LinearMap.ext h)
    set v := A e m1 with hvdef
    have hv0 : v ≠ 0 := hm1
    have hve : A e v = v := by rw [hvdef, ← hmulA, hband e]
    have hleft : ∀ x : S, A x v = A (e * x) v := by
      intro x; rw [hmulA, hve]
    set J : JClass S := ⟨greenClass e, e, rfl⟩ with hJ
    have hJg : J.val = greenClass e := rfl
    -- the submodule U
    let U : Submodule K M := LinearMap.ker (A e) ⊓ ⨅ t : S, LinearMap.ker (A e ∘ₗ A t)
    have hmemU : ∀ m, m ∈ U ↔ A e m = 0 ∧ ∀ t, A e (A t m) = 0 := by
      intro m
      simp [U, Submodule.mem_iInf]
    have hUinv : SemigroupInvariant rho U := by
      intro s m hm
      rw [hmemU] at hm ⊢
      refine ⟨hm.2 s, fun t => ?_⟩
      rw [← hmulA s t]; exact hm.2 _
    have hU : U = ⊥ := by
      rcases hirr U hUinv with h | h
      · exact h
      · exfalso
        have : v ∈ U := by rw [h]; trivial
        rw [hmemU] at this
        exact hv0 (by rw [← hve]; exact this.1)
    have hAe : ∀ x : S, A e (A x v) = A (e * x * e) v := by
      intro x
      rw [← hmulA x e, hleft (x * e)]; simp only [mul_assoc]
    -- Claim A
    have hclaim : ∀ s : S, A s v = scalarCharacter K J s • v := by
      intro s
      have hw : A s v - scalarCharacter K J s • v ∈ U := by
        rw [hmemU]
        by_cases hs : e * s * e = e
        · rw [X7T_sc_one hband J e hJg _ hs, one_smul]
          refine ⟨?_, fun t => ?_⟩
          · rw [map_sub, hAe s, hs, hve, sub_self]
          · rw [map_sub, map_sub, ← hmulA s t, hAe (s * t), hAe t]
            by_cases hst : e * (s * t) * e = e
            · rw [hst, X7T_mul_right hband e s t hst, sub_self]
            · have hte : e * t * e ≠ e := fun h => hst (X7T_mul e s t hband hs h)
              rcases hdich (s * t) with h1 | h1
              · rcases hdich t with h2 | h2
                · rw [h1, h2]; simp
                · exact absurd h2 hte
              · exact absurd h1 hst
        · rw [X7T_sc_zero hband J e hJg _ hs, zero_smul, sub_zero]
          refine ⟨?_, fun t => ?_⟩
          · rw [hAe s]
            rcases hdich s with h1 | h1
            · rw [h1]; rfl
            · exact absurd h1 hs
          · rw [← hmulA s t, hAe (s * t)]
            rcases hdich (s * t) with h1 | h1
            · rw [h1]; rfl
            · exact absurd (X7T_mul_left hband e s t h1) hs
      rw [hU, Submodule.mem_bot, sub_eq_zero] at hw
      exact hw
    -- span
    have hspan : Submodule.span K {v} = ⊤ := by
      rcases hirr (Submodule.span K {v}) (by
        intro s m hm
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
        rw [map_smul, hclaim, smul_smul]
        exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩) with h | h
      · exfalso
        have : v ∈ Submodule.span K {v} := Submodule.mem_span_singleton_self v
        rw [h, Submodule.mem_bot] at this
        exact hv0 this
      · exact h
    have hall : ∀ (s : S) (m : M), A s m = scalarCharacter K J s • m := by
      intro s m
      have hm : m ∈ Submodule.span K {v} := by rw [hspan]; trivial
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm
      rw [map_smul, hclaim, smul_smul, smul_smul, mul_comm]
    have hrank : Module.finrank K M = 1 := by
      rw [← finrank_top K M, ← hspan, finrank_span_singleton hv0]
    have hfin : FiniteDimensional K M := Module.finite_of_finrank_eq_succ hrank
    have hann : semigroupAnnihilator rho = classIdeal J := by
      ext s
      simp only [semigroupAnnihilator, Set.mem_ofPred_eq]
      rw [X7T_mem_classIdeal hband J e hJg]
      constructor
      · intro h hs
        have := h v
        rw [← hA, hall, X7T_sc_one hband J e hJg _ hs, one_smul] at this
        exact hv0 this
      · intro hs m
        rw [← hA, hall, X7T_sc_zero hband J e hJg _ hs, zero_smul]
    have hapex : HasApex rho J := ⟨⟨e, (rfl : principalIdeal e = principalIdeal e), hband e⟩, hann⟩
    refine ⟨hfin, hrank, J, ⟨hapex, ?_⟩, ?_⟩
    · let g : K ≃ₗ[K] M := (LinearEquiv.toSpanNonzeroSingleton K M v hv0).trans
        (LinearEquiv.ofTop _ hspan)
      have hg : ∀ c : K, g c = c • v := fun c => rfl
      refine ⟨g.symm, fun s m => ?_⟩
      conv_lhs => rw [← g.apply_symm_apply m, hg]
      rw [← hA, hall, smul_smul, ← hg, LinearEquiv.symm_apply_apply]
    · rintro J' ⟨⟨_, hJ'⟩, _⟩
      obtain ⟨g', hg'⟩ := J'.property
      have hiff : ∀ s : S, g' * s * g' ≠ g' ↔ e * s * e ≠ e := by
        intro s
        rw [← X7T_mem_classIdeal hband J' g' hg', ← X7T_mem_classIdeal hband J e hJg, ← hJ', hann]
      have h1 : e * g' * e = e := by
        by_contra h
        exact ((hiff g').mpr h) (by rw [hband g', hband g'])
      have h2 : g' * e * g' = g' := by
        by_contra h
        exact ((hiff e).mp h) (by rw [hband e, hband e])
      rw [← X7T_mem_iff hband] at h1 h2
      apply Subtype.ext
      rw [hg', hJg]
      have hPI : principalIdeal g' = principalIdeal e := by
        ext x; exact ⟨fun hx => X7T_trans hx h2, fun hx => X7T_trans hx h1⟩
      simp only [greenClass, hPI]
