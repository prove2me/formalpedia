-- Prove2me | solution 1 for SubnormalCover.multiplicity_ge_minFac
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-14T13:05:31.327536+00:00
-- url     : https://prove2.me/submissions/06c4673f-3dad-4fdd-8422-fc92c77c8cd7

import Mathlib
import Definitions.Def_SubnormalCover_uniformCover
import Definitions.Def_BFFPyramidal_arithmetic

/-!
# Theorem 4.3(i) — the mission goal

Self-contained: every supporting result is inlined below, each in its own namespace, exactly as
developed.  The public declaration is `solution`.
-/

open SubnormalCover BFFPyramidal Pointwise

/-! Supporting development for the Sun subnormal-cover mission.  Everything here is complete;
it is split into per-theorem submission files at the end. -/

namespace SunDev
open BFFPyramidal SubnormalCover Pointwise



/-- Normal case: `(N ⊓ B).index ∣ N.index * B.index`, from the second isomorphism theorem. -/
private lemma inf_index_dvd_of_normal {G : Type*} [Group G] (N B : Subgroup G) [N.Normal] :
    (N ⊓ B).index ∣ N.index * B.index := by
  have h1 : (N ⊓ B).relIndex B * B.index = (N ⊓ B).index :=
    Subgroup.relIndex_mul_index inf_le_right
  have h2 : (N ⊓ B).relIndex B = N.relIndex B := Subgroup.inf_relIndex_right N B
  have h3 : N.relIndex B ∣ N.index := Subgroup.relIndex_dvd_index_of_normal N B
  rw [← h1, h2]
  exact mul_dvd_mul h3 dvd_rfl

private lemma inf_subgroupOf_distrib {G : Type*} [Group G] (A B K : Subgroup G) :
    (A ⊓ B).subgroupOf K = A.subgroupOf K ⊓ B.subgroupOf K := Subgroup.map_subtype_inj.mp rfl

/-- **Lemma 2.1, binary form.**  If `A` is subnormal then `[G : A ⊓ B] ∣ [G : A] · [G : B]`
for *every* subgroup `B`.  Only `A` needs to be subnormal. -/
theorem inf_index_dvd_of_isSubnormal {G : Type*} [Group G] {A : Subgroup G}
    (hA : A.IsSubnormal) : ∀ B : Subgroup G, (A ⊓ B).index ∣ A.index * B.index := by
  induction hA with
  | top => intro B; simp
  | step A K hle hSubn hN ih =>
    intro B
    -- `C = K ⊓ B`, and `A ⊓ B = A ⊓ C`
    have hAC : A ⊓ B = A ⊓ (K ⊓ B) := by
      rw [← inf_assoc, inf_eq_left.mpr hle]
    -- inside `K`, `A` is normal, so the normal case applies
    have hin : ((A ⊓ (K ⊓ B)).subgroupOf K).index
        ∣ (A.subgroupOf K).index * ((K ⊓ B).subgroupOf K).index := by
      rw [inf_subgroupOf_distrib]
      exact inf_index_dvd_of_normal (A.subgroupOf K) ((K ⊓ B).subgroupOf K)
    have e1 : (A ⊓ (K ⊓ B)).relIndex K * K.index = (A ⊓ (K ⊓ B)).index :=
      Subgroup.relIndex_mul_index (le_trans inf_le_left hle)
    have e2 : (K ⊓ B).relIndex K * K.index = (K ⊓ B).index :=
      Subgroup.relIndex_mul_index inf_le_left
    have e3 : A.relIndex K * K.index = A.index := Subgroup.relIndex_mul_index hle
    -- assemble
    have hstep : (A ⊓ (K ⊓ B)).index ∣ A.relIndex K * (K ⊓ B).index := by
      calc (A ⊓ (K ⊓ B)).index = (A ⊓ (K ⊓ B)).relIndex K * K.index := e1.symm
        _ ∣ (A.relIndex K * (K ⊓ B).relIndex K) * K.index :=
            mul_dvd_mul hin dvd_rfl
        _ = A.relIndex K * ((K ⊓ B).relIndex K * K.index) := by ring
        _ = A.relIndex K * (K ⊓ B).index := by rw [e2]
    calc (A ⊓ B).index = (A ⊓ (K ⊓ B)).index := by rw [hAC]
      _ ∣ A.relIndex K * (K ⊓ B).index := hstep
      _ ∣ A.relIndex K * (K.index * B.index) := mul_dvd_mul dvd_rfl (ih B)
      _ = (A.relIndex K * K.index) * B.index := by ring
      _ = A.index * B.index := by rw [e3]


/-- The engine: for a finite set `P` of integers `≥ 2` with lower bound `m` and upper bound `M`
(and `m ≤ M + 1` to cover `P = ∅`), `(m-1) ∏_{p ∈ P} p ≤ M ∏_{p ∈ P} (p-1)`. -/
private lemma prod_pred_bound : ∀ P : Finset ℕ, (∀ p ∈ P, 2 ≤ p) → ∀ m M : ℕ,
    (∀ p ∈ P, m ≤ p) → (∀ p ∈ P, p ≤ M) → m ≤ M + 1 →
    (m - 1) * ∏ p ∈ P, p ≤ M * ∏ p ∈ P, (p - 1) := by
  intro P
  induction P using Finset.induction_on_max with
  | empty => intro _ m M _ _ hmM; simpa using by omega
  | insert a s hlt ih =>
    intro h2 m M hm hM hmM
    have hane : a ∉ s := fun h => absurd (hlt a h) (lt_irrefl a)
    have h2a : 2 ≤ a := h2 a (Finset.mem_insert_self a s)
    have hma : m ≤ a := hm a (Finset.mem_insert_self a s)
    have haM : a ≤ M := hM a (Finset.mem_insert_self a s)
    have hprod : ∏ p ∈ insert a s, p = a * ∏ p ∈ s, p := Finset.prod_insert hane
    have hprod' : ∏ p ∈ insert a s, (p - 1) = (a - 1) * ∏ p ∈ s, (p - 1) :=
      Finset.prod_insert hane
    have ihs : (m - 1) * ∏ p ∈ s, p ≤ (a - 1) * ∏ p ∈ s, (p - 1) := by
      refine ih (fun p hp => h2 p (Finset.mem_insert_of_mem hp)) m (a - 1)
        (fun p hp => hm p (Finset.mem_insert_of_mem hp))
        (fun p hp => by have := hlt p hp; omega) (by omega)
    rw [hprod, hprod']
    calc (m - 1) * (a * ∏ p ∈ s, p) = a * ((m - 1) * ∏ p ∈ s, p) := by ring
      _ ≤ a * ((a - 1) * ∏ p ∈ s, (p - 1)) := Nat.mul_le_mul_left _ ihs
      _ ≤ M * ((a - 1) * ∏ p ∈ s, (p - 1)) := Nat.mul_le_mul_right _ haM

theorem minFac_pred_mul_prod_le {N : ℕ} (hN : 2 ≤ N) :
    (Nat.minFac N - 1) * ∏ p ∈ N.primeFactors, p
      ≤ maxPrimeFac N * ∏ p ∈ N.primeFactors, (p - 1) := by
  have hN0 : N ≠ 0 := by omega
  have hmemMin : Nat.minFac N ∈ N.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd N, hN0⟩
  have hle : ∀ p ∈ N.primeFactors, p ≤ maxPrimeFac N := fun p hp =>
    Finset.le_sup (f := id) hp
  refine prod_pred_bound N.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le) _ _
    (fun p hp => Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le
      (Nat.dvd_of_mem_primeFactors hp)) hle ?_
  exact le_trans (hle _ hmemMin) (Nat.le_succ _)


private lemma mem_divisorClosure {R : Finset ℕ} {d : ℕ} :
    d ∈ divisorClosure R ↔ ∃ m ∈ R, d ∣ m ∧ m ≠ 0 := by
  simp [divisorClosure, Nat.mem_divisors]

private lemma muMeasure_singleton (m : ℕ) : muMeasure (divisorClosure {m}) = m := by
  simp [muMeasure, divisorClosure, Nat.sum_totient]

private lemma muMeasure_union_add_inter (A B : Finset ℕ) :
    muMeasure (A ∪ B) + muMeasure (A ∩ B) = muMeasure A + muMeasure B :=
  Finset.sum_union_inter

private lemma divisorClosure_insert (m : ℕ) (R : Finset ℕ) :
    divisorClosure (insert m R) = divisorClosure {m} ∪ divisorClosure R := by
  simp [divisorClosure, Finset.biUnion_insert]

/-- `D R ∩ D {m} = D {gcd r m : r ∈ R}` when `m ≠ 0` and no member of `R` is zero. -/
private lemma divisorClosure_inter {m : ℕ} (hm : m ≠ 0) (R : Finset ℕ) (hR : ∀ r ∈ R, r ≠ 0) :
    divisorClosure R ∩ divisorClosure {m} = divisorClosure (R.image fun r => Nat.gcd r m) := by
  ext d
  simp only [Finset.mem_inter, mem_divisorClosure, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨r, hr, hdr, -⟩, ⟨m', hm', hdm, -⟩⟩
    rw [hm'] at hdm
    exact ⟨Nat.gcd r m, ⟨r, hr, rfl⟩, Nat.dvd_gcd hdr hdm,
      fun h => hm (Nat.eq_zero_of_gcd_eq_zero_right h)⟩
  · rintro ⟨g, ⟨r, hr, rfl⟩, hdg, -⟩
    exact ⟨⟨r, hr, hdg.trans (Nat.gcd_dvd_left r m), hR r hr⟩,
      ⟨m, rfl, hdg.trans (Nat.gcd_dvd_right r m), hm⟩⟩

private lemma inter_biUnion_id {α : Type*} [DecidableEq α] (T : Finset α)
    (Δ : Finset (Finset α)) :
    T ∩ Δ.biUnion id = (Δ.image fun S => S ∩ T).biUnion id := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_image, id]
  constructor
  · rintro ⟨hxT, S, hS, hxS⟩; exact ⟨S ∩ T, ⟨S, hS, rfl⟩, Finset.mem_inter.mpr ⟨hxS, hxT⟩⟩
  · rintro ⟨X, ⟨S, hS, rfl⟩, hx⟩
    obtain ⟨hxS, hxT⟩ := Finset.mem_inter.mp hx
    exact ⟨hxT, S, hS, hxS⟩

/-- **Lemma 3.2.** -/
theorem muMeasure_ncard_biUnion {α : Type*} [DecidableEq α] (Γ : Set (Finset α))
    (hinter : ∀ S ∈ Γ, ∀ T ∈ Γ, S ∩ T ∈ Γ)
    (hcard : ∀ S ∈ Γ, ∀ T ∈ Γ, (S ∩ T).card = Nat.gcd S.card T.card)
    (Δ : Finset (Finset α)) (hΔ : ↑Δ ⊆ Γ) :
    (Δ.biUnion id).card = muMeasure (divisorClosure (Δ.image Finset.card)) := by
  classical
  by_cases hemp : ∃ S ∈ Δ, S = (∅ : Finset α)
  · -- degenerate: one member is empty, hence all are, and both sides vanish
    obtain ⟨S, hS, rfl⟩ := hemp
    have hall : ∀ T ∈ Δ, T = (∅ : Finset α) := by
      intro T hT
      have h := hcard ∅ (hΔ hS) T (hΔ hT)
      simp only [Finset.empty_inter, Finset.card_empty, Nat.gcd_zero_left] at h
      exact Finset.card_eq_zero.mp h.symm
    have h1 : Δ.biUnion id = (∅ : Finset α) :=
      Finset.eq_empty_of_forall_notMem fun x hx => by
        obtain ⟨T, hT, hxT⟩ := Finset.mem_biUnion.mp hx
        rw [hall T hT] at hxT; simp at hxT
    have h3 : divisorClosure (Δ.image Finset.card) = ∅ :=
      Finset.eq_empty_of_forall_notMem fun d hd => by
        obtain ⟨m, hm, -, hm0⟩ := mem_divisorClosure.mp hd
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hm
        exact hm0 (by simp [hall T hT])
    simp [h1, h3, muMeasure]
  · push_neg at hemp
    -- strong induction on the size of the family
    suffices H : ∀ n : ℕ, ∀ Δ : Finset (Finset α), Δ.card ≤ n → ↑Δ ⊆ Γ →
        (∀ S ∈ Δ, S.Nonempty) →
        (Δ.biUnion id).card = muMeasure (divisorClosure (Δ.image Finset.card)) from
      H Δ.card Δ le_rfl hΔ hemp
    intro n
    induction n with
    | zero =>
      intro Δ hc _ _
      have : Δ = ∅ := Finset.card_eq_zero.mp (by omega)
      subst this; simp [divisorClosure, muMeasure]
    | succ n ih =>
      intro Δ hc hΓ hnz
      rcases Δ.eq_empty_or_nonempty with rfl | ⟨T, hT⟩
      · simp [divisorClosure, muMeasure]
      set Δ' := Δ.erase T with hΔ'def
      have hTnot : T ∉ Δ' := Finset.notMem_erase T Δ
      have hins : Δ = insert T Δ' := (Finset.insert_erase hT).symm
      have hc' : Δ'.card ≤ n := by
        have h9 : Δ'.card + 1 = Δ.card := Finset.card_erase_add_one hT
        omega
      have hTΓ : T ∈ Γ := hΓ hT
      have hΓ' : ↑Δ' ⊆ Γ := fun S hS => hΓ (Finset.mem_of_mem_erase hS)
      have hnz' : ∀ S ∈ Δ', S.Nonempty := fun S hS => hnz S (Finset.mem_of_mem_erase hS)
      have hTc : T.card ≠ 0 := (Finset.card_pos.mpr (hnz T hT)).ne'
      -- the intersected family
      set Δ'' : Finset (Finset α) := Δ'.image (fun S => S ∩ T) with hΔ''def
      have hΓ'' : ↑Δ'' ⊆ Γ := by
        intro X hX
        simp only [hΔ''def, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hX
        obtain ⟨S, hS, rfl⟩ := hX
        exact hinter S (hΓ' hS) T hTΓ
      have hcard'' : ∀ S ∈ Δ', (S ∩ T).card = Nat.gcd S.card T.card :=
        fun S hS => hcard S (hΓ' hS) T hTΓ
      have hnz'' : ∀ X ∈ Δ'', X.Nonempty := by
        intro X hX
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hX
        refine Finset.card_pos.mp ?_
        have h8 : (S ∩ T).card = Nat.gcd S.card T.card := hcard'' S hS
        have h7 : S.card ≠ 0 := (Finset.card_pos.mpr (hnz' S hS)).ne'
        have : Nat.gcd S.card T.card ≠ 0 := Nat.gcd_ne_zero_left h7
        omega
      have hc'' : Δ''.card ≤ n := le_trans (Finset.card_image_le) hc'
      -- the two inductive calls
      have ih' := ih Δ' hc' hΓ' hnz'
      have ih'' := ih Δ'' hc'' hΓ'' hnz''
      -- cardinal bookkeeping
      have hU : (Δ.biUnion id).card + (T ∩ Δ'.biUnion id).card
          = T.card + (Δ'.biUnion id).card := by
        rw [hins, Finset.biUnion_insert]
        simpa using Finset.card_union_add_card_inter T (Δ'.biUnion id)
      have himg'' : Δ''.image Finset.card = (Δ'.image Finset.card).image fun r => Nat.gcd r T.card := by
        rw [hΔ''def, Finset.image_image, Finset.image_image]
        exact Finset.image_congr fun S hS => hcard'' S hS
      have hRnz : ∀ r ∈ Δ'.image Finset.card, r ≠ 0 := by
        intro r hr
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hr
        exact (Finset.card_pos.mpr (hnz' S hS)).ne'
      have hinter2 : divisorClosure (Δ''.image Finset.card)
          = divisorClosure (Δ'.image Finset.card) ∩ divisorClosure {T.card} := by
        rw [himg'', divisorClosure_inter hTc _ hRnz]
      have hunion2 : divisorClosure (Δ.image Finset.card)
          = divisorClosure {T.card} ∪ divisorClosure (Δ'.image Finset.card) := by
        rw [hins, Finset.image_insert, divisorClosure_insert]
      have hmu := muMeasure_union_add_inter (divisorClosure {T.card})
        (divisorClosure (Δ'.image Finset.card))
      rw [inter_biUnion_id T Δ', ← hΔ''def] at hU
      rw [ih'', hinter2, Finset.inter_comm] at hU
      rw [ih'] at hU
      rw [hunion2]
      rw [muMeasure_singleton] at hmu
      omega

/-- `|{x < h : d ∣ x}| = h / d` when `d ∣ h`. -/
theorem card_filter_dvd_range {h d : ℕ} (hd : d ∣ h) (hd0 : d ≠ 0) :
    ((Finset.range h).filter fun x => d ∣ x).card = h / d := by
  classical
  have himg : (Finset.range (h / d)).image (fun q => d * q)
      = (Finset.range h).filter fun x => d ∣ x := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨?_, Dvd.intro q rfl⟩
      calc d * q < d * (h / d) := by
            exact (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hd0)).mpr hq
        _ = h := Nat.mul_div_cancel' hd
    · rintro ⟨hx, q, rfl⟩
      exact ⟨q, by
        have : d * q < d * (h / d) := by rw [Nat.mul_div_cancel' hd]; exact hx
        exact Nat.lt_of_mul_lt_mul_left this, rfl⟩
  rw [← himg, Finset.card_image_of_injective _ (fun a b hab => by
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) hab), Finset.card_range]

/-- `gcd (h/m) (h/n) = h / lcm m n` for `m, n ∣ h`. -/
theorem gcd_div_div {h m n : ℕ} (hh : h ≠ 0) (hm : m ∣ h) (hn : n ∣ h) :
    Nat.gcd (h / m) (h / n) = h / Nat.lcm m n := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hh (Nat.eq_zero_of_zero_dvd hm)
  have hn0 : n ≠ 0 := by rintro rfl; exact hh (Nat.eq_zero_of_zero_dvd hn)
  have hL : Nat.lcm m n ∣ h := Nat.lcm_dvd hm hn
  have hL0 : Nat.lcm m n ≠ 0 := Nat.lcm_ne_zero hm0 hn0
  refine Nat.dvd_antisymm ?_ ?_
  · -- gcd ∣ h / lcm
    set g := Nat.gcd (h / m) (h / n) with hg
    have h1 : m * g ∣ h := (Nat.dvd_div_iff_mul_dvd hm).mp (Nat.gcd_dvd_left _ _)
    have h2 : n * g ∣ h := (Nat.dvd_div_iff_mul_dvd hn).mp (Nat.gcd_dvd_right _ _)
    have h3 : Nat.lcm (m * g) (n * g) ∣ h := Nat.lcm_dvd h1 h2
    have h4 : Nat.lcm (m * g) (n * g) = Nat.lcm m n * g := by
      simp [Nat.lcm_mul_right]
    rw [h4] at h3
    exact (Nat.dvd_div_iff_mul_dvd hL).mpr (by rwa [mul_comm] at h3 ⊢)
  · -- h / lcm ∣ gcd
    have key : ∀ a b : ℕ, 0 < a → a ∣ b → b ∣ h → h / b ∣ h / a := by
      intro a b ha hab hbh
      obtain ⟨v, rfl⟩ := hab
      obtain ⟨u, hu⟩ := hbh
      have hb0 : 0 < a * v := by
        rcases Nat.eq_zero_or_pos (a * v) with h0 | h0
        · exact absurd (by rw [hu, h0, zero_mul]) hh
        · exact h0
      have hdb : h / (a * v) = u := by rw [hu, Nat.mul_div_cancel_left _ hb0]
      have hda : h / a = v * u := by
        rw [hu, mul_assoc, Nat.mul_div_cancel_left _ ha]
      rw [hdb, hda]
      exact Dvd.intro_left v rfl
    exact Nat.dvd_gcd (key m (Nat.lcm m n) (Nat.pos_of_ne_zero hm0) (Nat.dvd_lcm_left m n) hL)
      (key n (Nat.lcm m n) (Nat.pos_of_ne_zero hn0) (Nat.dvd_lcm_right m n) hL)

/-! ### Lemma 2.1, k-ary form -/

theorem index_iInf_dvd_prod_finset {G : Type*} [Group G] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (K : ι → Subgroup G) (hsn : ∀ i ∈ s, (K i).IsSubnormal) :
    (⨅ i ∈ s, K i).index ∣ ∏ i ∈ s, (K i).index := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hsplit : (⨅ i ∈ insert a s, K i) = K a ⊓ ⨅ i ∈ s, K i := Finset.iInf_insert a s K
    rw [hsplit, Finset.prod_insert ha]
    refine dvd_trans (inf_index_dvd_of_isSubnormal
      (hsn a (Finset.mem_insert_self a s)) (⨅ i ∈ s, K i)) ?_
    exact mul_dvd_mul dvd_rfl (ih fun i hi => hsn i (Finset.mem_insert_of_mem hi))

theorem index_iInf_dvd_prod {G : Type*} [Group G] {k : ℕ} (K : Fin k → Subgroup G)
    (hsn : ∀ i, (K i).IsSubnormal) (hfin : ∀ i, (K i).FiniteIndex) :
    (⨅ i, K i).index ∣ ∏ i, (K i).index := by
  classical
  have h := index_iInf_dvd_prod_finset (Finset.univ : Finset (Fin k)) K (fun i _ => hsn i)
  simpa using h

/-! ### Lemma 3.3 -/

theorem muMeasure_divisorClosure_relIndex {G : Type*} [Group G] (H : Subgroup G)
    (hfin : H.FiniteIndex) {k : ℕ} (K : Fin k → Subgroup G) (hHK : ∀ i, H ≤ K i) :
    muMeasure (divisorClosure (Finset.univ.image fun i => H.relIndex (K i)))
      = ((Finset.range H.index).filter fun n => ∃ i, (K i).index ∣ n).card := by
  classical
  set h := H.index with hhdef
  have hh0 : h ≠ 0 := hfin.index_ne_zero
  -- each index divides h, and the relative index is the cofactor
  have hdvd : ∀ i, (K i).index ∣ h := fun i => Subgroup.index_dvd_of_le (hHK i)
  have hni0 : ∀ i, (K i).index ≠ 0 := by
    intro i hi
    exact hh0 (Nat.eq_zero_of_zero_dvd (hi ▸ hdvd i))
  have hrel : ∀ i, H.relIndex (K i) = h / (K i).index := by
    intro i
    have hmul := Subgroup.relIndex_mul_index (hHK i)
    rw [hhdef, ← hmul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (hni0 i))]
  -- the family of "arithmetic progressions" inside `range h`
  set X : ℕ → Finset ℕ := fun d => (Finset.range h).filter (fun x => d ∣ x) with hXdef
  set Γ : Set (Finset ℕ) := {Y | ∃ d, d ∣ h ∧ Y = X d} with hΓdef
  have hXcard : ∀ d, d ∣ h → (X d).card = h / d := by
    intro d hd
    exact card_filter_dvd_range hd (fun h0 => hh0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hd)))
  have hXinter : ∀ m n : ℕ, X m ∩ X n = X (Nat.lcm m n) := by
    intro m n
    ext x
    simp only [hXdef, Finset.mem_inter, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hx, hm⟩, ⟨-, hn⟩⟩; exact ⟨hx, Nat.lcm_dvd hm hn⟩
    · rintro ⟨hx, hl⟩
      exact ⟨⟨hx, (Nat.dvd_lcm_left m n).trans hl⟩, ⟨hx, (Nat.dvd_lcm_right m n).trans hl⟩⟩
  have hinterΓ : ∀ S ∈ Γ, ∀ T ∈ Γ, S ∩ T ∈ Γ := by
    rintro S ⟨m, hm, rfl⟩ T ⟨n, hn, rfl⟩
    exact ⟨Nat.lcm m n, Nat.lcm_dvd hm hn, hXinter m n⟩
  have hcardΓ : ∀ S ∈ Γ, ∀ T ∈ Γ, (S ∩ T).card = Nat.gcd S.card T.card := by
    rintro S ⟨m, hm, rfl⟩ T ⟨n, hn, rfl⟩
    rw [hXinter m n, hXcard _ (Nat.lcm_dvd hm hn), hXcard m hm, hXcard n hn,
      gcd_div_div hh0 hm hn]
  -- the subfamily coming from the `K i`
  set Δ : Finset (Finset ℕ) := Finset.univ.image (fun i : Fin k => X ((K i).index)) with hΔdef
  have hΔΓ : ↑Δ ⊆ Γ := by
    intro Y hY
    simp only [hΔdef, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at hY
    obtain ⟨i, rfl⟩ := hY
    exact ⟨(K i).index, hdvd i, rfl⟩
  have hmain := muMeasure_ncard_biUnion Γ hinterΓ hcardΓ Δ hΔΓ
  -- identify both sides
  have hbi : Δ.biUnion id = (Finset.range h).filter fun n => ∃ i, (K i).index ∣ n := by
    ext x
    simp only [hΔdef, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, id,
      Finset.mem_filter, Finset.mem_range, hXdef]
    constructor
    · rintro ⟨Y, ⟨i, rfl⟩, hx⟩
      obtain ⟨hlt, hdv⟩ := Finset.mem_filter.mp hx
      exact ⟨Finset.mem_range.mp hlt, i, hdv⟩
    · rintro ⟨hlt, i, hdv⟩
      exact ⟨X ((K i).index), ⟨i, rfl⟩, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hdv⟩⟩
  have himg : Δ.image Finset.card = Finset.univ.image fun i => H.relIndex (K i) := by
    rw [hΔdef, Finset.image_image]
    refine Finset.image_congr ?_
    intro i _
    simp only [Function.comp_apply]
    rw [hXcard _ (hdvd i), hrel i]
  rw [hbi, himg] at hmain
  exact hmain.symm

/-! ### Lemma 2.2 and Corollary 2.1 -/

section Core
variable {G : Type*} [Group G]

private lemma map_conj_self {H : Subgroup G} {h : G} (hh : h ∈ H) :
    H.map ((MulAut.conj h : MulAut G) : G →* G) = H := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show h * y * h⁻¹ ∈ H
    exact H.mul_mem (H.mul_mem hh hy) (H.inv_mem hh)
  · intro hx
    refine ⟨h⁻¹ * x * h, H.mul_mem (H.mul_mem (H.inv_mem hh) hx) hh, ?_⟩
    show h * (h⁻¹ * x * h) * h⁻¹ = x
    group

private lemma map_conj_mul_mem {H : Subgroup G} {a h : G} (hh : h ∈ H) :
    H.map ((MulAut.conj (a * h) : MulAut G) : G →* G)
      = H.map ((MulAut.conj a : MulAut G) : G →* G) := by
  have hcomp : ((MulAut.conj (a * h) : MulAut G) : G →* G)
      = ((MulAut.conj a : MulAut G) : G →* G).comp ((MulAut.conj h : MulAut G) : G →* G) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, ← Subgroup.map_map, map_conj_self hh]

private lemma normalCore_eq_iInf_out (H : Subgroup G) :
    H.normalCore = ⨅ q : G ⧸ H, H.map ((MulAut.conj (Quotient.out q) : MulAut G) : G →* G) := by
  rw [H.normalCore_eq_iInf_map_conj]
  refine le_antisymm (le_iInf fun q => iInf_le _ _) (le_iInf fun g => ?_)
  have hq : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk g : G ⧸ H)) : G ⧸ H)
      = QuotientGroup.mk g := Quotient.out_eq _
  have hmem : (Quotient.out (QuotientGroup.mk g : G ⧸ H))⁻¹ * g ∈ H :=
    QuotientGroup.eq.mp hq
  have heq : H.map ((MulAut.conj g : MulAut G) : G →* G)
      = H.map ((MulAut.conj (Quotient.out (QuotientGroup.mk g : G ⧸ H)) : MulAut G) : G →* G) := by
    set a := Quotient.out (QuotientGroup.mk g : G ⧸ H) with ha
    have : g = a * (a⁻¹ * g) := by group
    rw [this, map_conj_mul_mem hmem]
  rw [heq]
  exact iInf_le _ _

/-- Conjugation preserves the index. -/
private lemma index_map_conj (H : Subgroup G) (g : G) :
    (H.map ((MulAut.conj g : MulAut G) : G →* G)).index = H.index :=
  Subgroup.index_map_equiv H (MulAut.conj g)

/-- **Lemma 2.2.** -/
theorem primeFactors_normalCore_index (H : Subgroup G)
    (hsn : H.IsSubnormal) (hfin : H.FiniteIndex) :
    (H.normalCore.index).primeFactors = H.index.primeFactors := by
  classical
  haveI := hfin
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hk0 : H.index ≠ 0 := hfin.index_ne_zero
  have hcard0 : (Finset.univ : Finset (G ⧸ H)).card ≠ 0 := by
    simp only [Finset.card_univ, ne_eq, Fintype.card_eq_zero_iff]
    exact fun h => h.false (QuotientGroup.mk (1 : G))
  have hcore : H.normalCore
      = ⨅ q ∈ (Finset.univ : Finset (G ⧸ H)),
          H.map ((MulAut.conj (Quotient.out q) : MulAut G) : G →* G) := by
    rw [normalCore_eq_iInf_out]; simp
  have hdvd : H.normalCore.index ∣ H.index ^ (Finset.univ : Finset (G ⧸ H)).card := by
    rw [hcore]
    refine dvd_trans (index_iInf_dvd_prod_finset Finset.univ _
      (fun q _ => hsn.map (MulEquiv.surjective (MulAut.conj (Quotient.out q))))) ?_
    simp only [index_map_conj, Finset.prod_const]
    exact dvd_rfl
  have hdvd2 : H.index ∣ H.normalCore.index := Subgroup.index_dvd_of_le H.normalCore_le
  have hcore0 : H.normalCore.index ≠ 0 := fun h =>
    (pow_ne_zero (Finset.univ : Finset (G ⧸ H)).card hk0) (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  refine Finset.Subset.antisymm ?_ (Nat.primeFactors_mono hdvd2 hcore0)
  calc H.normalCore.index.primeFactors
      ⊆ (H.index ^ (Finset.univ : Finset (G ⧸ H)).card).primeFactors :=
        Nat.primeFactors_mono hdvd (pow_ne_zero _ hk0)
    _ = H.index.primeFactors := by rw [Nat.primeFactors_pow _ hcard0]

/-- **Corollary 2.1.**  A subnormal Hall subgroup is normal. -/
theorem normal_of_isSubnormal_of_coprime [Finite G] (H : Subgroup G)
    (hsn : H.IsSubnormal) (hHall : Nat.Coprime (Nat.card H) H.index) :
    H.Normal := by
  classical
  haveI hfi : H.FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hkey := primeFactors_normalCore_index H hsn hfi
  have hle : H.normalCore ≤ H := H.normalCore_le
  have hmul : H.normalCore.relIndex H * H.index = H.normalCore.index :=
    Subgroup.relIndex_mul_index hle
  have hdvdH : H.normalCore.relIndex H ∣ Nat.card H := Subgroup.relIndex_dvd_card _ _
  have hcore0 : H.normalCore.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hone : H.normalCore.relIndex H = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpcore : p ∣ H.normalCore.index := hmul ▸ Dvd.dvd.mul_right hpdvd _
    have hmem : p ∈ H.index.primeFactors := by
      rw [← hkey]; exact Nat.mem_primeFactors.mpr ⟨hp, hpcore, hcore0⟩
    have h1 : p ∣ Nat.card H := hpdvd.trans hdvdH
    have h2 : p ∣ H.index := Nat.dvd_of_mem_primeFactors hmem
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hHall ▸ Nat.dvd_gcd h1 h2))
  have heq : H.normalCore = H :=
    le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)
  rw [← heq]
  exact H.normalCore_normal

end Core

/-! ### Lemma 4.1 for uniform covers -/

section Cover
variable {G : Type*} [Group G] {k : ℕ}

open scoped Classical in
private lemma card_eq_filter (K : Fin k → Subgroup G) (a : Fin k → G) (x : G) :
    Nat.card {i : Fin k // (a i)⁻¹ * x ∈ K i}
      = (Finset.univ.filter fun i => (a i)⁻¹ * x ∈ K i).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Lemma 4.1** for uniform covers: since the covering function is constant, the union of the
parts indexed by `I` is right-invariant under `⨅ j ∉ I, K j`, i.e. it is a union of left cosets
of that subgroup. -/
theorem isUniformCover_mul_mem_biUnion
    (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ) (hcov : IsUniformCover K a w)
    (I : Set (Fin k)) {x y : G}
    (hx : x ∈ ⋃ i ∈ I, (a i) • (K i : Set G))
    (hy : y ∈ ⨅ j ∈ Iᶜ, K j) :
    x * y ∈ ⋃ i ∈ I, (a i) • (K i : Set G) := by
  classical
  -- membership in a coset, spelled arithmetically
  have hmem : ∀ (z : G) (i : Fin k), z ∈ (a i) • (K i : Set G) ↔ (a i)⁻¹ * z ∈ K i := by
    intro z i
    constructor
    · rintro ⟨u, hu, rfl⟩; simpa using hu
    · intro h; refine ⟨(a i)⁻¹ * z, h, ?_⟩; show a i * ((a i)⁻¹ * z) = z; group
  set S : G → Finset (Fin k) := fun z => Finset.univ.filter fun i => (a i)⁻¹ * z ∈ K i with hS
  have hcard : ∀ z, (S z).card = w := by
    intro z
    have h1 : Nat.card {i : Fin k // (a i)⁻¹ * z ∈ K i} = (S z).card := by
      rw [hS, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← h1]; exact hcov z
  -- outside `I` the membership pattern is unchanged
  have hy' : ∀ j ∉ I, y ∈ K j := by
    intro j hj
    have h := Subgroup.mem_iInf.mp hy j
    exact Subgroup.mem_iInf.mp h hj
  have hout : ∀ j ∉ I, ((a j)⁻¹ * (x * y) ∈ K j ↔ (a j)⁻¹ * x ∈ K j) := by
    intro j hj
    have hyj : y ∈ K j := hy' j hj
    constructor
    · intro h
      have : ((a j)⁻¹ * (x * y)) * y⁻¹ ∈ K j := (K j).mul_mem h ((K j).inv_mem hyj)
      simpa [mul_assoc] using this
    · intro h
      have : ((a j)⁻¹ * x) * y ∈ K j := (K j).mul_mem h hyj
      simpa [mul_assoc] using this
  have hfilt : (S (x * y)).filter (fun i => i ∉ I) = (S x).filter (fun i => i ∉ I) := by
    ext j
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(hout j h2).mp h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(hout j h2).mpr h1, h2⟩
  -- split each count into the part inside `I` and the part outside
  have hsplit : ∀ z, ((S z).filter (fun i => i ∈ I)).card
      + ((S z).filter (fun i => i ∉ I)).card = w := by
    intro z
    rw [Finset.card_filter_add_card_filter_not (s := S z) (p := fun i => i ∈ I)]
    exact hcard z
  have hIeq : ((S (x * y)).filter (fun i => i ∈ I)).card
      = ((S x).filter (fun i => i ∈ I)).card := by
    have h1 := hsplit (x * y)
    have h2 := hsplit x
    rw [hfilt] at h1
    omega
  -- `x` lies in one of the parts indexed by `I`
  obtain ⟨i, hiI, hxi⟩ : ∃ i ∈ I, (a i)⁻¹ * x ∈ K i := by
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨i, hiI, hxi⟩ := hx
    exact ⟨i, hiI, (hmem x i).mp hxi⟩
  have hpos : 0 < ((S x).filter (fun i => i ∈ I)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨by simp [hS, hxi], hiI⟩⟩
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < ((S (x * y)).filter (fun i => i ∈ I)).card)
  obtain ⟨hjS, hjI⟩ := Finset.mem_filter.mp hj
  refine Set.mem_biUnion hjI ((hmem (x * y) j).mpr ?_)
  simpa [hS] using hjS

end Cover

end SunDev

/-!
# Z.-W. Sun, *On the Herzog-Schönheim conjecture for uniform covers of groups*, Theorem 3.1

Let `H ≤ G` be of finite index, let `K 1, …, K k` be subnormal subgroups of `G` containing
`H`, and let `a 1, …, a k ∈ G`.  Then the number of left cosets of `H` contained in
`⋃ i, a i K i` is at least

  `|{0 ≤ n < [G : H] : [G : K i] ∣ n for some i}|`.

The proof follows the paper: by Lemma 3.3 the right-hand side is `μ (D {[K i : H]})`, and
one inducts on `[G : H]`.  Here the induction is run in the "relative" form suggested by
Berger–Felzenbaum–Fraenkel's Lemma IV: the ambient group `G` and the subgroup `H` stay fixed
and the induction is on `[N : H]` for an intermediate subgroup `H ≤ N ≤ G`.

Organisation of the file.

* Part 0 : the scaling law `μ (D (p · R)) = p · μ (D R)` (Sun's Lemma 3.1).  This is available
  on the platform as `BFFPyramidal.muMeasure_divisorClosure_image_mul`, which is imported
  above; but that reference file is only a statement stub locally, so a self-contained
  complete copy of the proof from `Solutions/Sol_BFF_mu_scaling.lean` is included here and
  is what the main theorem actually uses.
* Part 1 : the calculus of `μ` and `D`, culminating in the arithmetic inequality `key_arith`.
* Part 2 : counting left cosets of `H`.
* Part 3 : the group theory - existence of a maximal normal subgroup and the subnormal
  dichotomy `K ≤ N₁ ∨ K ⊔ N₁ = N`.
* Part 4 : the induction and the theorem.
-/

namespace SunT31_B

open Pointwise BFFPyramidal Finset

/-! ## Part 0 : the scaling law -/

/-- Membership in the divisor closure. -/
private lemma mem_divisorClosure_iff {R : Finset ℕ} {d : ℕ} :
    d ∈ divisorClosure R ↔ ∃ m ∈ R, d ∣ m ∧ m ≠ 0 := by
  simp [divisorClosure, Nat.mem_divisors]

/-- The basic divisibility reformulation: `N ∣ m * j` iff the order `N / gcd N j` divides `m`. -/
private lemma dvd_mul_iff_div_gcd_dvd {N : ℕ} (hN : 0 < N) (j m : ℕ) :
    N ∣ m * j ↔ N / N.gcd j ∣ m := by
  have hgpos : 0 < N.gcd j := by
    rcases Nat.eq_zero_or_pos (N.gcd j) with h | h
    · rw [Nat.gcd_eq_zero_iff] at h; omega
    · exact h
  have hgN : N.gcd j ∣ N := Nat.gcd_dvd_left N j
  have hgj : N.gcd j ∣ j := Nat.gcd_dvd_right N j
  have hNg : N / N.gcd j * N.gcd j = N := Nat.div_mul_cancel hgN
  have hjg : j / N.gcd j * N.gcd j = j := Nat.div_mul_cancel hgj
  have hcop : Nat.Coprime (N / N.gcd j) (j / N.gcd j) := Nat.coprime_div_gcd_div_gcd hgpos
  constructor
  · intro h
    have h2 : N / N.gcd j * N.gcd j ∣ m * (j / N.gcd j) * N.gcd j := by
      rw [hNg, mul_assoc, hjg]; exact h
    have h3 : N / N.gcd j ∣ m * (j / N.gcd j) :=
      (Nat.mul_dvd_mul_iff_right hgpos).mp h2
    exact hcop.dvd_of_dvd_mul_right h3
  · intro h
    have h2 : N / N.gcd j * N.gcd j ∣ m * j := mul_dvd_mul h hgj
    rwa [hNg] at h2

/-- Counting interpretation of `μ (D R)`: if every member of `R` divides `N > 0`, then
`μ (D R)` is the number of `j < N` killed by some `m ∈ R`. -/
private lemma count_eq_muMeasure (N : ℕ) (hN : 0 < N) (R : Finset ℕ) (hdvd : ∀ m ∈ R, m ∣ N) :
    #{j ∈ range N | ∃ m ∈ R, N ∣ m * j} = muMeasure (divisorClosure R) := by
  have hpos : ∀ m ∈ R, m ≠ 0 := by
    intro m hm h
    exact hN.ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd m hm))
  have hsub : divisorClosure R ⊆ N.divisors := by
    intro d hd
    obtain ⟨m, hm, hdm, hm0⟩ := mem_divisorClosure_iff.mp hd
    exact Nat.mem_divisors.mpr ⟨hdm.trans (hdvd m hm), hN.ne'⟩
  have hfil : {j ∈ range N | ∃ m ∈ R, N ∣ m * j}
      = {j ∈ range N | N / N.gcd j ∈ divisorClosure R} := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨m, hm, h⟩
      exact mem_divisorClosure_iff.mpr
        ⟨m, hm, (dvd_mul_iff_div_gcd_dvd hN j m).mp h, hpos m hm⟩
    · intro h
      obtain ⟨m, hm, hdm, -⟩ := mem_divisorClosure_iff.mp h
      exact ⟨m, hm, (dvd_mul_iff_div_gcd_dvd hN j m).mpr hdm⟩
  rw [hfil]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun j => N.gcd j) (t := N.divisors)
    (fun x _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hN.ne'⟩)]
  have step : ∀ c ∈ N.divisors,
      #{j ∈ {j ∈ range N | N / N.gcd j ∈ divisorClosure R} | N.gcd j = c}
        = if N / c ∈ divisorClosure R then Nat.totient (N / c) else 0 := by
    intro c hc
    rw [Finset.filter_filter]
    by_cases hmem : N / c ∈ divisorClosure R
    · rw [if_pos hmem, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hc)]
      congr 1
      apply Finset.filter_congr
      intro j _
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hmem, h⟩
    · rw [if_neg hmem, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ h
      exact hmem (h.2 ▸ h.1)
  rw [Finset.sum_congr rfl step]
  rw [Nat.sum_div_divisors N (fun d => if d ∈ divisorClosure R then Nat.totient d else 0)]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  rfl

/-- A sum of a function of period `N` over `range (k * N)` is `k` times its sum over `range N`. -/
private lemma sum_range_mul_of_periodic (N : ℕ) (g : ℕ → ℕ) (hg : ∀ j, g (j % N) = g j) :
    ∀ k : ℕ, ∑ j ∈ range (k * N), g j = k * ∑ j ∈ range N, g j := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hkN : (k + 1) * N = k * N + N := by ring
    rw [hkN, Finset.sum_range_add, ih]
    have hshift : ∀ x ∈ range N, g (k * N + x) = g x := by
      intro x _
      have hmod : (k * N + x) % N = x % N := by
        rw [Nat.add_comm, Nat.mul_comm]
        exact Nat.add_mul_mod_self_left x N k
      rw [← hg (k * N + x), hmod, hg x]
    rw [Finset.sum_congr rfl hshift]
    ring

/-- Sun's Lemma 3.1 (Berger–Felzenbaum–Fraenkel): `μ (D (p · R)) = p · μ (D R)`. -/
private theorem mu_scaling (k : ℕ) (hk : 0 < k) (R : Finset ℕ) (hR : ∀ m ∈ R, 0 < m) :
    muMeasure (divisorClosure (R.image (fun m => k * m)))
      = k * muMeasure (divisorClosure R) := by
  classical
  set N := ∏ m ∈ R, m with hNdef
  have hN : 0 < N := Finset.prod_pos hR
  have hdvd : ∀ m ∈ R, m ∣ N := fun m hm => Finset.dvd_prod_of_mem _ hm
  have hkN : 0 < k * N := Nat.mul_pos hk hN
  have hdvd' : ∀ m' ∈ R.image (fun m => k * m), m' ∣ k * N := by
    intro m' hm'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
    exact Nat.mul_dvd_mul_left k (hdvd m hm)
  rw [← count_eq_muMeasure N hN R hdvd, ← count_eq_muMeasure (k * N) hkN _ hdvd']
  have hpred : {j ∈ range (k * N) | ∃ m' ∈ R.image (fun m => k * m), k * N ∣ m' * j}
      = {j ∈ range (k * N) | ∃ m ∈ R, N ∣ m * j} := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨m', hm', h⟩
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
      refine ⟨m, hm, ?_⟩
      rw [mul_assoc] at h
      exact (Nat.mul_dvd_mul_iff_left hk).mp h
    · rintro ⟨m, hm, h⟩
      refine ⟨k * m, Finset.mem_image_of_mem _ hm, ?_⟩
      rw [mul_assoc]
      exact Nat.mul_dvd_mul_left k h
  rw [hpred, Finset.card_filter, Finset.card_filter]
  have hg : ∀ j, (if ∃ m ∈ R, N ∣ m * (j % N) then 1 else 0)
      = (if ∃ m ∈ R, N ∣ m * j then 1 else 0) := by
    intro j
    have hiff : (∃ m ∈ R, N ∣ m * (j % N)) ↔ (∃ m ∈ R, N ∣ m * j) := by
      refine exists_congr fun m => and_congr_right fun _ => ?_
      have h : m * (j % N) ≡ m * j [MOD N] := Nat.ModEq.mul_left m (Nat.mod_modEq j N)
      rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
      exact ⟨fun hx => h.symm.trans hx, fun hx => h.trans hx⟩
    simp only [hiff]
  exact sum_range_mul_of_periodic N _ hg k

/-! ## Part 1 : the calculus of `μ` and `D` -/

private lemma muMeasure_mono {S T : Finset ℕ} (h : S ⊆ T) : muMeasure S ≤ muMeasure T :=
  Finset.sum_le_sum_of_subset h

/-- Inclusion–exclusion for `μ`, in the form `μ (S ∪ T) = μ S + μ (T \ S)`. -/
private lemma muMeasure_union (S T : Finset ℕ) :
    muMeasure (S ∪ T) = muMeasure S + muMeasure (T \ S) := by
  unfold muMeasure
  rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]

private lemma muMeasure_union_le (S T : Finset ℕ) :
    muMeasure (S ∪ T) ≤ muMeasure S + muMeasure T := by
  rw [muMeasure_union]
  exact Nat.add_le_add_left (muMeasure_mono Finset.sdiff_subset) _

/-- `D (R ∪ S) = D R ∪ D S`. -/
private lemma divisorClosure_union (R S : Finset ℕ) :
    divisorClosure (R ∪ S) = divisorClosure R ∪ divisorClosure S := by
  ext d
  simp only [divisorClosure, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨m, hm | hm, h⟩
    · exact Or.inl ⟨m, hm, h⟩
    · exact Or.inr ⟨m, hm, h⟩
  · rintro (⟨m, hm, h⟩ | ⟨m, hm, h⟩)
    · exact ⟨m, Or.inl hm, h⟩
    · exact ⟨m, Or.inr hm, h⟩

private lemma divisorClosure_mono {R S : Finset ℕ} (h : R ⊆ S) :
    divisorClosure R ⊆ divisorClosure S :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

private lemma divisorClosure_biUnion {κ : Type*} [DecidableEq κ] (J : Finset κ)
    (B : κ → Finset ℕ) :
    divisorClosure (J.biUnion B) = J.biUnion (fun j => divisorClosure (B j)) := by
  ext d
  simp only [divisorClosure, Finset.mem_biUnion]
  constructor
  · rintro ⟨m, ⟨j, hj, hm⟩, h⟩; exact ⟨j, hj, m, hm, h⟩
  · rintro ⟨j, hj, m, hm, h⟩; exact ⟨m, ⟨j, hj, hm⟩, h⟩

private lemma muMeasure_biUnion_le {κ : Type*} [DecidableEq κ] (J : Finset κ)
    (Y : κ → Finset ℕ) :
    muMeasure (J.biUnion Y) ≤ ∑ j ∈ J, muMeasure (Y j) := by
  classical
  induction J using Finset.induction with
  | empty => simp [muMeasure]
  | @insert j J hj ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hj]
      exact (muMeasure_union_le _ _).trans (Nat.add_le_add_left ih _)

private lemma biUnion_sdiff_eq {κ : Type*} [DecidableEq κ] (J : Finset κ) (Y : κ → Finset ℕ)
    (X : Finset ℕ) : J.biUnion (fun j => Y j \ X) = (J.biUnion Y) \ X := by
  ext d
  simp only [Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨j, hj, h1, h2⟩; exact ⟨⟨j, hj, h1⟩, h2⟩
  · rintro ⟨⟨j, hj, h1⟩, h2⟩; exact ⟨j, hj, h1, h2⟩

/-- `D R ⊆ D (p · R)` for `p > 0`. -/
private lemma divisorClosure_subset_image_mul {p : ℕ} (hp : 0 < p) (A : Finset ℕ) :
    divisorClosure A ⊆ divisorClosure (A.image (fun m => p * m)) := by
  intro d hd
  obtain ⟨m, hm, hdm, hm0⟩ := mem_divisorClosure_iff.mp hd
  exact mem_divisorClosure_iff.mpr ⟨p * m, Finset.mem_image_of_mem _ hm,
    hdm.trans ⟨p, by ring⟩, Nat.mul_ne_zero hp.ne' hm0⟩

/-- The arithmetic heart of Theorem 3.1 (p. 161 of the paper): if `#J = p` then
`μ (D (p·A ∪ ⋃ⱼ Bⱼ)) ≤ ∑ⱼ μ (D (A ∪ Bⱼ))`. -/
private lemma key_arith {κ : Type*} [DecidableEq κ] {p : ℕ} (hp : 0 < p)
    (A : Finset ℕ) (hA : ∀ m ∈ A, 0 < m) (J : Finset κ) (hJ : J.card = p)
    (B : κ → Finset ℕ) :
    muMeasure (divisorClosure (A.image (fun m => p * m) ∪ J.biUnion B))
      ≤ ∑ j ∈ J, muMeasure (divisorClosure (A ∪ B j)) := by
  classical
  set X := divisorClosure A with hX
  set R₀ := A.image (fun m => p * m) with hR₀
  set Y := J.biUnion (fun j => divisorClosure (B j)) with hY
  have hDR₀ : muMeasure (divisorClosure R₀) = p * muMeasure X := mu_scaling p hp A hA
  have hXsub : X ⊆ divisorClosure R₀ := divisorClosure_subset_image_mul hp A
  have hlhs : muMeasure (divisorClosure (R₀ ∪ J.biUnion B))
      = p * muMeasure X + muMeasure (Y \ divisorClosure R₀) := by
    rw [divisorClosure_union, divisorClosure_biUnion, ← hY, muMeasure_union, hDR₀]
  have h1 : muMeasure (Y \ divisorClosure R₀) ≤ muMeasure (Y \ X) := by
    refine muMeasure_mono ?_
    intro d hd
    rw [Finset.mem_sdiff] at hd ⊢
    exact ⟨hd.1, fun h => hd.2 (hXsub h)⟩
  have hrhs : p * muMeasure X + muMeasure (Y \ X)
      ≤ ∑ j ∈ J, muMeasure (divisorClosure (A ∪ B j)) := by
    have e1 : ∀ j ∈ J, muMeasure (divisorClosure (A ∪ B j))
        = muMeasure X + muMeasure (divisorClosure (B j) \ X) := by
      intro j _
      rw [divisorClosure_union, ← hX, muMeasure_union]
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_const, hJ, smul_eq_mul]
    have h2 : muMeasure (Y \ X) ≤ ∑ j ∈ J, muMeasure (divisorClosure (B j) \ X) := by
      rw [hY, ← biUnion_sdiff_eq]
      exact muMeasure_biUnion_le _ _
    exact Nat.add_le_add_left h2 _
  calc muMeasure (divisorClosure (R₀ ∪ J.biUnion B))
      = p * muMeasure X + muMeasure (Y \ divisorClosure R₀) := hlhs
    _ ≤ p * muMeasure X + muMeasure (Y \ X) := Nat.add_le_add_left h1 _
    _ ≤ ∑ j ∈ J, muMeasure (divisorClosure (A ∪ B j)) := hrhs

/-- `μ (D {m}) = m` for `m > 0` (Gauss). -/
private lemma muMeasure_divisorClosure_singleton {m : ℕ} : muMeasure (divisorClosure {m}) = m := by
  simp [muMeasure, divisorClosure, Nat.sum_totient]

/-! ## Part 2 : counting left cosets of `H` -/

section Count

variable {G : Type*} [Group G]

/-- The number of left cosets of `H` meeting (equivalently, contained in, for the sets we use)
a subset `U` of `G`. -/
private noncomputable def cnt (H : Subgroup G) (U : Set G) : ℕ :=
  (QuotientGroup.mk '' U : Set (G ⧸ H)).ncard

private lemma cnt_mono {H : Subgroup G} [Finite (G ⧸ H)] {U V : Set G} (h : U ⊆ V) :
    cnt H U ≤ cnt H V :=
  Set.ncard_le_ncard (Set.image_mono h) (Set.toFinite _)

private lemma image_mk_smul (H : Subgroup G) (g : G) (U : Set G) :
    (QuotientGroup.mk '' (g • U) : Set (G ⧸ H)) = g • (QuotientGroup.mk '' U : Set (G ⧸ H)) := by
  ext q
  simp only [Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk u, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨r, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨g * u, ⟨u, hu, rfl⟩, rfl⟩

private lemma cnt_smul (H : Subgroup G) (g : G) (U : Set G) : cnt H (g • U) = cnt H U := by
  rw [cnt, cnt, image_mk_smul, Set.ncard_smul_set]

/-- The natural injection `N ⧸ (H ∩ N) ↪ G ⧸ H`. -/
private def cosetMap (H N : Subgroup G) : (↥N ⧸ (H.subgroupOf N)) → G ⧸ H := fun q =>
  Quotient.liftOn' q (fun x : ↥N => (QuotientGroup.mk (x : G) : G ⧸ H)) (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy
    have h : ((x : G))⁻¹ * (y : G) ∈ H := by
      have := Subgroup.mem_subgroupOf.mp hxy
      push_cast at this
      exact this
    exact (QuotientGroup.eq (s := H)).mpr h)

private lemma cosetMap_mk (H N : Subgroup G) (x : ↥N) :
    cosetMap H N (QuotientGroup.mk x) = (QuotientGroup.mk (x : G) : G ⧸ H) := rfl

private lemma cosetMap_injective (H N : Subgroup G) : Function.Injective (cosetMap H N) := by
  have key : ∀ x y : ↥N, cosetMap H N (QuotientGroup.mk x) = cosetMap H N (QuotientGroup.mk y) →
      (QuotientGroup.mk x : ↥N ⧸ (H.subgroupOf N)) = QuotientGroup.mk y := by
    intro x y h
    rw [cosetMap_mk, cosetMap_mk, QuotientGroup.eq] at h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    push_cast
    exact h
  intro q₁ q₂
  exact Quotient.inductionOn₂' q₁ q₂ key

private lemma range_cosetMap_subset (H N : Subgroup G) :
    Set.range (cosetMap H N) ⊆ (QuotientGroup.mk '' (N : Set G) : Set (G ⧸ H)) := by
  rintro q ⟨r, rfl⟩
  induction r using QuotientGroup.induction_on with
  | H x => exact ⟨(x : G), x.2, rfl⟩

/-- Lower bound for the base case: `N` contains `[N : H]` cosets of `H`. -/
private lemma relIndex_le_cnt {H N : Subgroup G} [Finite (G ⧸ H)] :
    H.relIndex N ≤ cnt H (N : Set G) := by
  have h1 : H.relIndex N = Nat.card (↥N ⧸ (H.subgroupOf N)) := Subgroup.index_eq_card _
  have h2 : Nat.card (↥N ⧸ (H.subgroupOf N)) = Nat.card (Set.range (cosetMap H N)) :=
    (Nat.card_range_of_injective (cosetMap_injective H N)).symm
  have h3 : Nat.card (Set.range (cosetMap H N)) = (Set.range (cosetMap H N)).ncard := rfl
  rw [h1, h2, h3]
  exact Set.ncard_le_ncard (range_cosetMap_subset H N) (Set.toFinite _)

/-- The cosets of `N₁` inside `N` cover `N`. -/
private lemma exists_coset_out {N N₁ : Subgroup G} {x : G} (hx : x ∈ N) :
    ∃ q : ↥N ⧸ (N₁.subgroupOf N), x ∈ (((q.out : ↥N) : G)) • (N₁ : Set G) := by
  refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [smul_eq_mul, SetLike.mem_coe]
  have h : (QuotientGroup.mk (QuotientGroup.mk (⟨x, hx⟩ : ↥N)).out : ↥N ⧸ N₁.subgroupOf N)
      = QuotientGroup.mk ⟨x, hx⟩ := QuotientGroup.out_eq' _
  have h2 := QuotientGroup.eq.mp h
  rw [Subgroup.mem_subgroupOf] at h2
  push_cast at h2
  exact h2

/-- Distinct classes give disjoint cosets. -/
private lemma coset_out_disjoint {N N₁ : Subgroup G} {q q' : ↥N ⧸ (N₁.subgroupOf N)}
    (h : ((((q.out : ↥N) : G)) • (N₁ : Set G) ∩ (((q'.out : ↥N) : G)) • (N₁ : Set G)).Nonempty) :
    q = q' := by
  obtain ⟨x, hx, hx'⟩ := h
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hx hx'
  simp only [smul_eq_mul, SetLike.mem_coe] at hx hx'
  have key : (((q.out : ↥N) : G))⁻¹ * (((q'.out : ↥N) : G)) ∈ N₁ := by
    have he : ((((q.out : ↥N) : G))⁻¹ * x) * ((((q'.out : ↥N) : G))⁻¹ * x)⁻¹
        = (((q.out : ↥N) : G))⁻¹ * (((q'.out : ↥N) : G)) := by group
    rw [← he]
    exact N₁.mul_mem hx (N₁.inv_mem hx')
  have h2 : (QuotientGroup.mk q.out : ↥N ⧸ N₁.subgroupOf N) = QuotientGroup.mk q'.out := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    push_cast
    exact key
  rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
  exact h2

/-- The fibrewise count of `H`-cosets over the cosets of `N₁` inside `N`. -/
private lemma cnt_eq_sum_cosets {H N N₁ : Subgroup G} [Finite (G ⧸ H)] (hHN₁ : H ≤ N₁)
    [Fintype (↥N ⧸ (N₁.subgroupOf N))] {U : Set G} (hU : U ⊆ (N : Set G)) :
    cnt H U = ∑ q : ↥N ⧸ (N₁.subgroupOf N),
      cnt H (U ∩ (((q.out : ↥N) : G)) • (N₁ : Set G)) := by
  classical
  set C : (↥N ⧸ (N₁.subgroupOf N)) → Set G :=
    fun q => (((q.out : ↥N) : G)) • (N₁ : Set G) with hC
  have hdisj : Pairwise (Function.onFun Disjoint
      fun q : ↥N ⧸ (N₁.subgroupOf N) =>
        (QuotientGroup.mk '' (U ∩ C q) : Set (G ⧸ H))) := by
    intro q q' hne
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    apply hne
    refine coset_out_disjoint (q := q) (q' := q') ⟨y, ?_, hy.2⟩
    have hmem : x⁻¹ * y ∈ H := by
      have := (QuotientGroup.eq (s := H)).mp hxy.symm
      exact this
    have hx1 : x ∈ (((q.out : ↥N) : G)) • (N₁ : Set G) := hx.2
    show y ∈ (((q.out : ↥N) : G)) • (N₁ : Set G)
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hx1 ⊢
    simp only [smul_eq_mul, SetLike.mem_coe] at hx1 ⊢
    have : (((q.out : ↥N) : G))⁻¹ * y
        = ((((q.out : ↥N) : G))⁻¹ * x) * (x⁻¹ * y) := by group
    rw [this]
    exact N₁.mul_mem hx1 (hHN₁ hmem)
  have hcover : (QuotientGroup.mk '' U : Set (G ⧸ H))
      = ⋃ q : ↥N ⧸ (N₁.subgroupOf N), (QuotientGroup.mk '' (U ∩ C q) : Set (G ⧸ H)) := by
    rw [← Set.image_iUnion, ← Set.inter_iUnion]
    congr 1
    refine (Set.inter_eq_self_of_subset_left ?_).symm
    intro x hx
    obtain ⟨q, hq⟩ := exists_coset_out (N₁ := N₁) (hU hx)
    exact Set.mem_iUnion.mpr ⟨q, hq⟩
  rw [cnt, hcover, Set.ncard_iUnion_of_finite (fun q => Set.toFinite _) hdisj,
    finsum_eq_sum_of_fintype]
  rfl

end Count

/-! ## Part 3 : the group theory -/

section GroupTheory

/-- A maximal proper normal subgroup containing a given proper subnormal subgroup `J` of finite
index, together with the *dichotomy* that any subnormal subgroup is either contained in it or
generates the whole group with it.  This is the analogue of Berger–Felzenbaum–Fraenkel's
Lemma II, and it is where subnormality is used. -/
private lemma exists_maximal_normal {Γ : Type*} [Group Γ] {J : Subgroup Γ}
    (hidx : J.index ≠ 0) (hJ : J.IsSubnormal) (hJne : J ≠ ⊤) :
    ∃ P : Subgroup Γ, P.Normal ∧ J ≤ P ∧ P ≠ ⊤ ∧
      ∀ A : Subgroup Γ, A.IsSubnormal → A ≤ P ∨ A ⊔ P = ⊤ := by
  classical
  obtain ⟨P₀, hP₀n, hJP₀, hP₀lt⟩ := hJ.exists_normal_and_le_and_lt_top_of_ne hJne
  set Pred : ℕ → Prop := fun m => ∃ P : Subgroup Γ, P.Normal ∧ J ≤ P ∧ P ≠ ⊤ ∧ P.index = m
    with hPred
  have hex : ∃ m, Pred m := ⟨P₀.index, P₀, hP₀n, hJP₀, hP₀lt.ne, rfl⟩
  obtain ⟨P, hPn, hJP, hPne, hPidx⟩ := Nat.find_spec hex
  have hmin : ∀ m, Pred m → Nat.find hex ≤ m := fun m hm => Nat.find_le hm
  have hPidx0 : P.index ≠ 0 := fun h =>
    hidx (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hJP))
  -- maximality
  have hmax : ∀ P' : Subgroup Γ, P'.Normal → P ≤ P' → P' ≠ ⊤ → P' = P := by
    intro P' hP'n hPP' hP'ne
    have hpred' : Pred P'.index := ⟨P', hP'n, hJP.trans hPP', hP'ne, rfl⟩
    have h1 : Nat.find hex ≤ P'.index := hmin _ hpred'
    have h2 : P.relIndex P' * P'.index = P.index := Subgroup.relIndex_mul_index hPP'
    rw [hPidx] at h2
    have h3 : P.relIndex P' = 1 := by
      rcases Nat.eq_zero_or_pos (P.relIndex P') with h | h
      · rw [h, zero_mul] at h2; exact absurd h2.symm (by rw [hPidx] at hPidx0; exact hPidx0)
      · by_contra hne
        have : 2 ≤ P.relIndex P' := by omega
        have hlt : 2 * P'.index ≤ Nat.find hex := by
          calc 2 * P'.index ≤ P.relIndex P' * P'.index := Nat.mul_le_mul_right _ this
            _ = Nat.find hex := h2
        have hP'0 : P'.index ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at h2
          rw [hPidx] at hPidx0
          exact hPidx0 h2.symm
        omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h3) hPP'
  refine ⟨P, hPn, hJP, hPne, ?_⟩
  intro A hA
  by_cases hsup : A ⊔ P = ⊤
  · exact Or.inr hsup
  refine Or.inl ?_
  have : P.Normal := hPn
  set π : Γ →* Γ ⧸ P := QuotientGroup.mk' P with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective P
  have hB : (A.map π).IsSubnormal := hA.map hsurj
  have hBne : A.map π ≠ ⊤ := by
    intro h
    apply hsup
    have := congrArg (Subgroup.comap π) h
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at this
  obtain ⟨C, hCn, hBC, hClt⟩ := hB.exists_normal_and_le_and_lt_top_of_ne hBne
  have hP'n : (C.comap π).Normal := hCn.comap π
  have hPP' : P ≤ C.comap π := by
    intro x hx
    have : π x = 1 := by
      rw [hπ]
      exact (QuotientGroup.eq_one_iff x).mpr hx
    simp only [Subgroup.mem_comap, this]
    exact C.one_mem
  have hP'ne : C.comap π ≠ ⊤ := by
    intro h
    apply hClt.ne
    have := congrArg (Subgroup.map π) h
    rwa [Subgroup.map_comap_eq_self_of_surjective hsurj, Subgroup.map_top_of_surjective _ hsurj]
      at this
  have := hmax _ hP'n hPP' hP'ne
  calc A ≤ Subgroup.comap π (A.map π) := Subgroup.le_comap_map π A
    _ ≤ Subgroup.comap π C := Subgroup.comap_mono hBC
    _ = P := this

/-- Sun's maximal normal subgroup `H*`, relativised to an intermediate subgroup `N`. -/
private lemma exists_max_normal_rel {G : Type*} [Group G] {H N J : Subgroup G}
    (hidx : H.relIndex N ≠ 0) (hHJ : H ≤ J) (hJN : J ≤ N) (hJne : J ≠ N)
    (hJsn : J.IsSubnormal) :
    ∃ N₁ : Subgroup G, H ≤ N₁ ∧ N₁ ≤ N ∧ N₁ ≠ N ∧ (N₁.subgroupOf N).Normal ∧
      ∀ A : Subgroup G, A ≤ N → A.IsSubnormal → (A ≤ N₁ ∨ A ⊔ N₁ = N) := by
  have hsubinj : Function.Injective (N.subtype) := N.subtype_injective
  have hJidx : (J.subgroupOf N).index ≠ 0 := by
    have hsplit : H.relIndex J * J.relIndex N = H.relIndex N :=
      Subgroup.relIndex_mul_relIndex H J N hHJ hJN
    intro h
    rw [show (J.subgroupOf N).index = J.relIndex N from rfl] at h
    rw [h, mul_zero] at hsplit
    exact hidx hsplit.symm
  have hJtop : J.subgroupOf N ≠ ⊤ := by
    rw [Ne, Subgroup.subgroupOf_eq_top]
    intro h
    exact hJne (le_antisymm hJN h)
  obtain ⟨P, hPn, hJP, hPne, hdich⟩ := exists_maximal_normal hJidx hJsn.subgroupOf hJtop
  refine ⟨P.map N.subtype, ?_, Subgroup.map_subtype_le P, ?_, ?_, ?_⟩
  · refine hHJ.trans ?_
    calc J = Subgroup.map N.subtype (J.subgroupOf N) := (Subgroup.map_subgroupOf_eq_of_le hJN).symm
      _ ≤ Subgroup.map N.subtype P := Subgroup.map_mono hJP
  · intro h
    apply hPne
    have : (Subgroup.map N.subtype P).subgroupOf N = P :=
      Subgroup.comap_map_eq_self_of_injective hsubinj P
    rw [h, Subgroup.subgroupOf_self] at this
    exact this.symm
  · have : (Subgroup.map N.subtype P).subgroupOf N = P :=
      Subgroup.comap_map_eq_self_of_injective hsubinj P
    rw [this]; exact hPn
  · intro A hAN hAsn
    rcases hdich (A.subgroupOf N) hAsn.subgroupOf with h | h
    · left
      calc A = Subgroup.map N.subtype (A.subgroupOf N) :=
            (Subgroup.map_subgroupOf_eq_of_le hAN).symm
        _ ≤ Subgroup.map N.subtype P := Subgroup.map_mono h
    · right
      have := congrArg (Subgroup.map N.subtype) h
      rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAN,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this

/-- Second isomorphism theorem, relative form: if `A ⊔ N₁ = N` with `N₁` normal in `N`, then
`[A : H] = [A ∩ N₁ : H] · [N : N₁]`. -/
private lemma relIndex_eq_mul_of_sup {G : Type*} [Group G] {H N N₁ A : Subgroup G}
    (hN₁N : N₁ ≤ N) (hAN : A ≤ N) (hHA : H ≤ A) (hHN₁ : H ≤ N₁)
    (hnorm : (N₁.subgroupOf N).Normal) (hsup : A ⊔ N₁ = N) :
    H.relIndex A = H.relIndex (A ⊓ N₁) * N₁.relIndex N := by
  have hsubinj : Function.Injective (N.subtype) := N.subtype_injective
  have hnorm' : (N₁.subgroupOf N).Normal := hnorm
  have htop : (A.subgroupOf N) ⊔ (N₁.subgroupOf N) = ⊤ := by
    apply Subgroup.map_injective hsubinj
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAN,
      Subgroup.map_subgroupOf_eq_of_le hN₁N, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup
  have key : (A ⊓ N₁).relIndex A = N₁.relIndex N := by
    have h1 : (N₁.subgroupOf N).relIndex ((A.subgroupOf N) ⊔ (N₁.subgroupOf N))
        = (N₁.subgroupOf N).relIndex (A.subgroupOf N) :=
      Subgroup.relIndex_sup_right _ _
    rw [htop, Subgroup.relIndex_top_right] at h1
    rw [← Subgroup.inf_relIndex_right] at h1
    have h2 : (N₁.subgroupOf N) ⊓ (A.subgroupOf N) = (N₁ ⊓ A).subgroupOf N :=
      (Subgroup.comap_inf _ _ _).symm
    rw [h2, Subgroup.relIndex_subgroupOf hAN] at h1
    rw [inf_comm]
    rw [show N₁.relIndex N = (N₁.subgroupOf N).index from rfl]
    exact h1.symm
  rw [← key]
  exact (Subgroup.relIndex_mul_relIndex H (A ⊓ N₁) A (le_inf hHA hHN₁) inf_le_left).symm

end GroupTheory

/-- The easy half of Sun's Lemma 2.1 / BFF's Lemma I: a point of `aK ∩ bL` spreads to a whole
coset of `K ⊓ L`. -/
private lemma smul_inf_subset {G : Type*} [Group G] (K L : Subgroup G) {a b x : G}
    (hx : x ∈ (a • (K : Set G)) ∩ (b • (L : Set G))) :
    x • ((K ⊓ L : Subgroup G) : Set G) ⊆ (a • (K : Set G)) ∩ (b • (L : Set G)) := by
  obtain ⟨hxK, hxL⟩ := hx
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hxK hxL
  simp only [smul_eq_mul, SetLike.mem_coe] at hxK hxL
  intro y hy
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hy
  simp only [smul_eq_mul, SetLike.mem_coe, Subgroup.mem_inf] at hy
  refine ⟨?_, ?_⟩
  · rw [Set.mem_smul_set_iff_inv_smul_mem]
    have h : (a⁻¹ * x) * (x⁻¹ * y) ∈ K := K.mul_mem hxK hy.1
    simpa [mul_assoc] using h
  · rw [Set.mem_smul_set_iff_inv_smul_mem]
    have h : (b⁻¹ * x) * (x⁻¹ * y) ∈ L := L.mul_mem hxL hy.2
    simpa [mul_assoc] using h

private lemma mem_self_smul {G : Type*} [Group G] (K : Subgroup G) (a : G) :
    a ∈ a • (K : Set G) := by
  have h : a • (1 : G) ∈ a • (K : Set G) :=
    Set.smul_mem_smul_set (SetLike.mem_coe.mpr K.one_mem)
  simpa using h

/-- If `K ⊔ N₁ = N` with `N₁` normal in `N`, then every coset `a • K` with `a ∈ N` meets every
coset `b • N₁` with `b ∈ N`. -/
private lemma spread_of_sup {G : Type*} [Group G] {N N₁ K : Subgroup G}
    (hN₁N : N₁ ≤ N) (hKN : K ≤ N) (hnorm : (N₁.subgroupOf N).Normal)
    (hsup : K ⊔ N₁ = N) {a b : G} (ha : a ∈ N) (hb : b ∈ N) :
    ((a • (K : Set G)) ∩ (b • (N₁ : Set G))).Nonempty := by
  have hnormzr : N ≤ Subgroup.normalizer (N₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₁N).mp hnorm
  have hcoe : ((N₁ ⊔ K : Subgroup G) : Set G) = (N₁ : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N₁ K (hKN.trans hnormzr)
  rw [sup_comm, hsup] at hcoe
  have hmem : b⁻¹ * a ∈ (N : Set G) := N.mul_mem (N.inv_mem hb) ha
  rw [hcoe] at hmem
  obtain ⟨m, hm, x, hx, hmx⟩ := hmem
  refine ⟨a * x⁻¹, ?_, ?_⟩
  · have := Set.smul_mem_smul_set (a := a) (SetLike.mem_coe.mpr (K.inv_mem hx))
    simpa [smul_eq_mul] using this
  · rw [Set.mem_smul_set_iff_inv_smul_mem]
    show b⁻¹ * (a * x⁻¹) ∈ N₁
    have he : b⁻¹ * (a * x⁻¹) = (b⁻¹ * a) * x⁻¹ := by group
    rw [he, ← hmx]
    simpa using hm

/-! ## Part 4 : the induction -/

set_option linter.style.haveILetI false in
/-- Theorem 3.1, relativised to an intermediate subgroup `N` and proved by induction on
`[N : H]`. -/
private lemma main {G : Type*} [Group G] {H : Subgroup G} (hfinH : H.index ≠ 0) {k : ℕ} :
    ∀ (n : ℕ) (N : Subgroup G), H ≤ N → N.IsSubnormal → H.relIndex N ≤ n →
    ∀ (s : Finset (Fin k)) (K : Fin k → Subgroup G) (a : Fin k → G),
      (∀ i ∈ s, H ≤ K i) → (∀ i ∈ s, K i ≤ N) → (∀ i ∈ s, (K i).IsSubnormal) →
      (∀ i ∈ s, a i ∈ N) →
      muMeasure (divisorClosure (s.image fun i => H.relIndex (K i)))
        ≤ cnt H (⋃ i ∈ s, a i • (K i : Set G)) := by
  classical
  haveI : H.FiniteIndex := ⟨hfinH⟩
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  intro n
  induction n with
  | zero =>
    intro N hHN _ hle s K a _ _ _ _
    exfalso
    have h := Subgroup.relIndex_mul_index hHN
    rw [Nat.le_zero.mp hle, zero_mul] at h
    exact hfinH h.symm
  | succ n ih =>
    intro N hHN hNsn hle s K a hHK hKN hsn haN
    have hrelN0 : H.relIndex N ≠ 0 := by
      intro h
      have h2 := Subgroup.relIndex_mul_index hHN
      rw [h, zero_mul] at h2
      exact hfinH h2.symm
    by_cases hall : ∀ i ∈ s, K i = N
    · -- every `K i` is `N`: both sides are `[N : H]`
      rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i₀, hi₀⟩
      · simp only [Finset.image_empty, divisorClosure, Finset.biUnion_empty, muMeasure,
          Finset.sum_empty]
        exact Nat.zero_le _
      · have himg : (s.image fun i => H.relIndex (K i)) = {H.relIndex N} := by
          ext m
          simp only [Finset.mem_image, Finset.mem_singleton]
          constructor
          · rintro ⟨i, hi, rfl⟩; rw [hall i hi]
          · rintro rfl; exact ⟨i₀, hi₀, by rw [hall i₀ hi₀]⟩
        have hunion : (⋃ i ∈ s, a i • (K i : Set G)) = (N : Set G) := by
          refine Set.Subset.antisymm (Set.iUnion₂_subset fun i hi => ?_) ?_
          · rw [hall i hi]
            intro y hy
            obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hy
            exact SetLike.mem_coe.mpr (N.mul_mem (haN i hi) hw)
          · intro y hy
            refine Set.mem_iUnion₂.mpr ⟨i₀, hi₀, ?_⟩
            rw [hall i₀ hi₀, Set.mem_smul_set_iff_inv_smul_mem]
            simp only [smul_eq_mul, SetLike.mem_coe]
            exact N.mul_mem (N.inv_mem (haN i₀ hi₀)) hy
        rw [himg, hunion, muMeasure_divisorClosure_singleton]
        exact relIndex_le_cnt
    · -- some `K j` is proper : descend to a maximal normal subgroup `N₁` of `N`
      push_neg at hall
      obtain ⟨j, hj, hjne⟩ := hall
      obtain ⟨N₁, hHN₁, hN₁N, hN₁ne, hnorm, hdich⟩ :=
        exists_max_normal_rel hrelN0 (hHK j hj) (hKN j hj) hjne (hsn j hj)
      obtain ⟨p, hpdef⟩ : ∃ p, N₁.relIndex N = p := ⟨_, rfl⟩
      have hmulp : H.relIndex N₁ * p = H.relIndex N := by
        rw [← hpdef]; exact Subgroup.relIndex_mul_relIndex H N₁ N hHN₁ hN₁N
      have hp0 : p ≠ 0 := by
        intro h; rw [h, mul_zero] at hmulp; exact hrelN0 hmulp.symm
      have hrel10 : H.relIndex N₁ ≠ 0 := by
        intro h; rw [h, zero_mul] at hmulp; exact hrelN0 hmulp.symm
      have hp2 : 2 ≤ p := by
        rcases Nat.lt_or_ge p 2 with h | h
        · exfalso
          have hp1 : p = 1 := by omega
          rw [hp1] at hpdef
          exact hN₁ne (le_antisymm hN₁N (Subgroup.relIndex_eq_one.mp hpdef))
        · exact h
      have hsmall : H.relIndex N₁ ≤ n := by
        have h2 : 2 * H.relIndex N₁ ≤ H.relIndex N₁ * p := by
          rw [mul_comm]; exact Nat.mul_le_mul_left _ hp2
        rw [hmulp] at h2
        have := Nat.one_le_iff_ne_zero.mpr hrel10
        omega
      have hN₁sn : N₁.IsSubnormal :=
        Subgroup.IsSubnormal.trans hN₁N (Subgroup.Normal.isSubnormal hnorm) hNsn
      haveI hfi : (N₁.subgroupOf N).FiniteIndex := by
        refine ⟨?_⟩
        show (N₁.subgroupOf N).index ≠ 0
        rw [show (N₁.subgroupOf N).index = N₁.relIndex N from rfl, hpdef]
        exact hp0
      haveI : Finite (↥N ⧸ (N₁.subgroupOf N)) := Subgroup.finite_quotient_of_finiteIndex
      letI : Fintype (↥N ⧸ (N₁.subgroupOf N)) := Fintype.ofFinite _
      set U : Set G := ⋃ i ∈ s, a i • (K i : Set G) with hU
      set C : (↥N ⧸ (N₁.subgroupOf N)) → Set G :=
        fun q => (((q.out : ↥N) : G)) • (N₁ : Set G) with hC
      set s₀ : Finset (Fin k) := s.filter (fun i => ¬ (K i ≤ N₁)) with hs₀
      set sq : (↥N ⧸ (N₁.subgroupOf N)) → Finset (Fin k) :=
        fun q => s.filter (fun i => K i ≤ N₁ ∧ a i ∈ C q) with hsq
      set A : Finset ℕ := s₀.image (fun i => H.relIndex (K i ⊓ N₁)) with hA
      set B : (↥N ⧸ (N₁.subgroupOf N)) → Finset ℕ :=
        fun q => (sq q).image (fun i => H.relIndex (K i)) with hB
      have hs₀s : s₀ ⊆ s := by rw [hs₀]; exact Finset.filter_subset _ _
      have hsqs : ∀ q, sq q ⊆ s := by intro q; rw [hsq]; exact Finset.filter_subset _ _
      have hUN : U ⊆ (N : Set G) := by
        rw [hU]
        refine Set.iUnion₂_subset fun i hi => ?_
        intro y hy
        obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hy
        exact SetLike.mem_coe.mpr (N.mul_mem (haN i hi) (hKN i hi hw))
      -- (A) the bound inside a single coset of `N₁`
      have key : ∀ q, muMeasure (divisorClosure (A ∪ B q)) ≤ cnt H (U ∩ C q) := by
        intro q
        set b : G := ((q.out : ↥N) : G) with hb
        have hbN : b ∈ N := q.out.2
        set T : Finset (Fin k) := s₀ ∪ sq q with hT
        have hTs : T ⊆ s := by
          intro i hi
          rcases Finset.mem_union.mp hi with h | h
          · exact hs₀s h
          · exact hsqs q h
        have hne : ∀ i ∈ T, ∃ x, x ∈ (a i • (K i : Set G)) ∩ C q := by
          intro i hi
          rcases Finset.mem_union.mp hi with h | h
          · rw [hs₀, Finset.mem_filter] at h
            have hsup : K i ⊔ N₁ = N := by
              rcases hdich (K i) (hKN i h.1) (hsn i h.1) with hle' | hs'
              · exact absurd hle' h.2
              · exact hs'
            exact spread_of_sup hN₁N (hKN i h.1) hnorm hsup (haN i h.1) hbN
          · rw [hsq] at h
            simp only [Finset.mem_filter] at h
            exact ⟨a i, mem_self_smul _ _, h.2.2⟩
        set c : Fin k → G := fun i =>
          if h : ∃ x, x ∈ (a i • (K i : Set G)) ∩ C q then b⁻¹ * h.choose else 1 with hc
        have hcmem : ∀ i ∈ T, c i ∈ N₁ ∧ b * c i ∈ (a i • (K i : Set G)) ∩ C q := by
          intro i hi
          have h : ∃ x, x ∈ (a i • (K i : Set G)) ∩ C q := hne i hi
          have hch : h.choose ∈ (a i • (K i : Set G)) ∩ C q := h.choose_spec
          have hcv : c i = b⁻¹ * h.choose := by simp only [hc]; exact dif_pos h
          have hbc : b * c i = h.choose := by rw [hcv]; group
          refine ⟨?_, ?_⟩
          · have h2 : h.choose ∈ b • (N₁ : Set G) := hch.2
            rw [Set.mem_smul_set_iff_inv_smul_mem] at h2
            rw [hcv]
            simpa using h2
          · rw [hbc]; exact hch
        have IH := ih N₁ (hHN₁) hN₁sn hsmall T (fun i => K i ⊓ N₁) c
          (fun i hi => le_inf (hHK i (hTs hi)) hHN₁) (fun i _ => inf_le_right)
          (fun i hi => Subgroup.IsSubnormal.inf (hsn i (hTs hi)) hN₁sn)
          (fun i hi => (hcmem i hi).1)
        have hsub : b • (⋃ i ∈ T, c i • ((K i ⊓ N₁ : Subgroup G) : Set G)) ⊆ U ∩ C q := by
          intro y hy
          obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hy
          obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz
          have hcm := hcmem i hi
          have hmem2 : b • z ∈ (b * c i) • ((K i ⊓ N₁ : Subgroup G) : Set G) := by
            obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hzi
            exact Set.mem_smul_set.mpr ⟨w, hw, by rw [smul_smul]⟩
          have hfin2 := smul_inf_subset (K i) N₁ hcm.2 hmem2
          refine ⟨?_, hfin2.2⟩
          rw [hU]
          exact Set.mem_iUnion₂.mpr ⟨i, hTs hi, hfin2.1⟩
        have hcount : cnt H (⋃ i ∈ T, c i • ((K i ⊓ N₁ : Subgroup G) : Set G))
            ≤ cnt H (U ∩ C q) := by
          calc cnt H (⋃ i ∈ T, c i • ((K i ⊓ N₁ : Subgroup G) : Set G))
              = cnt H (b • (⋃ i ∈ T, c i • ((K i ⊓ N₁ : Subgroup G) : Set G))) :=
                (cnt_smul H b _).symm
            _ ≤ cnt H (U ∩ C q) := cnt_mono hsub
        have himgT : T.image (fun i => H.relIndex (K i ⊓ N₁)) = A ∪ B q := by
          rw [hT, Finset.image_union, hA, hB]
          congr 1
          refine Finset.image_congr ?_
          intro i hi
          simp only [hsq, Finset.mem_coe, Finset.mem_filter] at hi
          show H.relIndex (K i ⊓ N₁) = H.relIndex (K i)
          rw [inf_eq_left.mpr hi.2.1]
        calc muMeasure (divisorClosure (A ∪ B q))
            = muMeasure (divisorClosure
                (T.image (fun i => H.relIndex (K i ⊓ N₁)))) := by rw [himgT]
          _ ≤ cnt H (⋃ i ∈ T, c i • ((K i ⊓ N₁ : Subgroup G) : Set G)) := IH
          _ ≤ cnt H (U ∩ C q) := hcount
      -- (B) the decomposition of the index set
      have hsdec : s ⊆ s₀ ∪ Finset.univ.biUnion sq := by
        intro i hi
        by_cases h : K i ≤ N₁
        · obtain ⟨q, hq⟩ := exists_coset_out (N := N) (N₁ := N₁) (haN i hi)
          refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ q, ?_⟩)
          rw [hsq]
          simp only [Finset.mem_filter]
          exact ⟨hi, h, hq⟩
        · refine Finset.mem_union_left _ ?_
          rw [hs₀, Finset.mem_filter]
          exact ⟨hi, h⟩
      have himg1 : s₀.image (fun i => H.relIndex (K i)) = A.image (fun m => p * m) := by
        rw [hA, Finset.image_image]
        refine Finset.image_congr ?_
        intro i hi
        simp only [hs₀, Finset.mem_coe, Finset.mem_filter] at hi
        have hsup : K i ⊔ N₁ = N := by
          rcases hdich (K i) (hKN i hi.1) (hsn i hi.1) with hle' | hs'
          · exact absurd hle' hi.2
          · exact hs'
        show H.relIndex (K i) = p * H.relIndex (K i ⊓ N₁)
        rw [relIndex_eq_mul_of_sup hN₁N (hKN i hi.1) (hHK i hi.1) hHN₁ hnorm hsup, hpdef,
          mul_comm]
      have himg2 : (Finset.univ.biUnion sq).image (fun i => H.relIndex (K i))
          = Finset.univ.biUnion B := by
        rw [Finset.biUnion_image, hB]
      have hJcard : (Finset.univ : Finset (↥N ⧸ (N₁.subgroupOf N))).card = p := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, ← hpdef]
        exact (Subgroup.index_eq_card (N₁.subgroupOf N)).symm
      have hApos : ∀ m ∈ A, 0 < m := by
        intro m hm
        rw [hA] at hm
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
        have hiS : i ∈ s := hs₀s hi
        have hle2 : H ≤ K i ⊓ N₁ := le_inf (hHK i hiS) hHN₁
        have := Subgroup.relIndex_mul_relIndex H (K i ⊓ N₁) N hle2 (inf_le_right.trans hN₁N)
        rcases Nat.eq_zero_or_pos (H.relIndex (K i ⊓ N₁)) with h | h
        · rw [h, zero_mul] at this; exact absurd this.symm hrelN0
        · exact h
      calc muMeasure (divisorClosure (s.image fun i => H.relIndex (K i)))
          ≤ muMeasure (divisorClosure
              ((s₀ ∪ Finset.univ.biUnion sq).image (fun i => H.relIndex (K i)))) :=
            muMeasure_mono (divisorClosure_mono (Finset.image_subset_image hsdec))
        _ = muMeasure (divisorClosure (A.image (fun m => p * m) ∪ Finset.univ.biUnion B)) := by
            rw [Finset.image_union, himg1, himg2]
        _ ≤ ∑ q : (↥N ⧸ (N₁.subgroupOf N)), muMeasure (divisorClosure (A ∪ B q)) :=
            key_arith (p := p) (by omega) A hApos Finset.univ hJcard B
        _ ≤ ∑ q : (↥N ⧸ (N₁.subgroupOf N)), cnt H (U ∩ C q) :=
            Finset.sum_le_sum (fun q _ => key q)
        _ = cnt H U := (cnt_eq_sum_cosets hHN₁ hUN).symm

/-! ## Part 5 : Theorem 3.1 -/

/-- **Sun, Theorem 3.1.**  Let `H` be a subgroup of finite index of a group `G`, let
`K 1, …, K k` be subnormal subgroups of `G` containing `H`, and let `a 1, …, a k ∈ G`.  Then
the number of left cosets of `H` contained in `⋃ i, a i K i` is at least the number of
`0 ≤ n < [G : H]` divisible by some `[G : K i]`. -/
theorem card_cosets_biUnion_ge {G : Type*} [Group G] (H : Subgroup G) (hfin : H.index ≠ 0)
    {k : ℕ} (K : Fin k → Subgroup G) (hHK : ∀ i, H ≤ K i)
    (hsn : ∀ i, (K i).IsSubnormal) (a : Fin k → G) :
    ((Finset.range H.index).filter fun n => ∃ i, (K i).index ∣ n).card
      ≤ ((QuotientGroup.mk '' (⋃ i, (a i) • (K i : Set G)) : Set (G ⧸ H))).ncard := by
  have hL := SunDev.muMeasure_divisorClosure_relIndex H ⟨hfin⟩ K hHK
  have hM := main (H := H) hfin (H.relIndex ⊤) ⊤ le_top Subgroup.IsSubnormal.top le_rfl
    Finset.univ K a (fun i _ => hHK i) (fun i _ => le_top) (fun i _ => hsn i)
    (fun i _ => Subgroup.mem_top _)
  have he : (⋃ i ∈ (Finset.univ : Finset (Fin k)), a i • (K i : Set G))
      = ⋃ i, a i • (K i : Set G) := by simp
  rw [he] at hM
  rw [← hL]
  exact hM

end SunT31_B

/-!
# Z.-W. Sun, *On the Herzog-Schönheim conjecture for uniform covers of groups*, Theorem 3.2

Case (a): all the `K i` are subnormal of finite index and `H` is normal of finite index, and
`⋃ i, a i (K i)` is a union of left cosets of `H`.  Writing `n i = [G : K i]`, `h = [G : H]`,
`g = (n 1, …, n k)`, `L = [n 1, …, n k]` and `M = sup_v |{i : n i = v}|`, the conclusion is

  `L ≤ M * (h, g) * σ (L / g)`,     `σ m = ∑_{d ∣ m} d`,

which is Sun's display (3.8) `g / (h, g) ≤ M * ∑_{d ∣ L/g} 1/d` cleared of denominators:
`∑_{d ∣ m} 1/d = σ m / m` (the involution `d ↦ m/d` on the divisors of `m`) and `g * (L/g) = L`
because `g ∣ n i ∣ L`, so multiplying (3.8) by the positive number `(h, g) * (L/g)` gives
exactly the displayed inequality, and conversely.

## Structure of the proof

The group-theoretic half follows the paper.  With `F = ⨅ i, K i` (of finite index by Lemma 2.1)
and `K i H = K i ⊔ H` (subnormal, since it is the preimage of the image of `K i` in `G ⧸ H`),
the hypothesis on `H` gives `⋃ i, a i (K i H) = ⋃ i, a i (K i)`, so Theorem 3.1 applied to the
family `K i H` over `F` yields, with `Q = [G : F]` and `m i = [G : K i H]`,

  `|{x < Q : ∃ i, m i ∣ x}| ≤ ∑ i, [K i : F] = ∑ i, Q / n i`.                            (⋆)

The arithmetic half replaces steps 2-3 of the paper (Lemma 3.4 and an infinite product of
geometric series) by an elementary counting argument.  Put `c = (h, g)`, `u = g / c` and
`r i = n i / u`; then `u * m i ∣ n i` — because `u * h = [h, g] ∣ [h, n i]` and
`m i ∣ (h, n i)`, while `[h, n i] * (h, n i) = h * n i` — so `m i ∣ r i` and the set counted
in (⋆) contains the multiples of the `r i`.  The key pointwise inequality is
`card_filter_dvd_le`: for `D = L / g`, every `x` satisfies

  `|{s ∈ R : s ∣ x}| ≤ |{d ∣ D : ∃ s ∈ R, d * s ∣ x}|`,     `R = {r 1, …, r k}`,

via the injection `s ↦ Y / s` where `Y` is the lcm of the members of `R` dividing `x`.
Summing this over `x < W = Q * D` and using that the counting function is linear along
multiples of a common multiple of `R` turns it into `D * (u * Σ) ≤ σ D * |{x < Q : ∃ i, r i ∣ x}|`
with `Σ = ∑_{s ∈ R} Q / (u * s)`, while (⋆) and the multiplicity bound `M` give the reverse
estimate `|{x < Q : ∃ i, r i ∣ x}| ≤ M * Σ`.  Cancelling `Σ > 0` gives `u * D ≤ σ D * M`, i.e.
`L = c * (u * D) ≤ M * c * σ D`.
-/

namespace SunT32_B

open SubnormalCover BFFPyramidal Pointwise

/-! ## Part 1 : counting -/

/-- The number of `x < W` divisible by some member of `R`. -/
private def cnt (R : Finset ℕ) (W : ℕ) : ℕ :=
  ((Finset.range W).filter fun x => ∃ s ∈ R, s ∣ x).card

/-- Double counting of a relation between two finsets. -/
private lemma double_count {α β : Type*} (s : Finset α) (t : Finset β)
    (p : α → β → Prop) [∀ a b, Decidable (p a b)] :
    ∑ a ∈ s, (t.filter fun b => p a b).card = ∑ b ∈ t, (s.filter fun a => p a b).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- The counting function is linear along multiples of a common multiple of `R`. -/
private lemma cnt_mul (R : Finset ℕ) {p : ℕ} (hp : ∀ s ∈ R, s ∣ p) (t : ℕ) :
    cnt R (t * p) = t * cnt R p := by
  classical
  induction t with
  | zero => simp [cnt]
  | succ t ih =>
      have hper : ∀ x : ℕ, (∃ s ∈ R, s ∣ t * p + x) ↔ (∃ s ∈ R, s ∣ x) := by
        intro x
        constructor
        · rintro ⟨s, hs, hsx⟩
          exact ⟨s, hs, (Nat.dvd_add_right (Dvd.dvd.mul_left (hp s hs) t)).mp hsx⟩
        · rintro ⟨s, hs, hsx⟩
          exact ⟨s, hs, Dvd.dvd.add (Dvd.dvd.mul_left (hp s hs) t) hsx⟩
      have hsucc : (t + 1) * p = t * p + p := by ring
      rw [hsucc]
      simp only [cnt, Finset.card_filter] at *
      rw [Finset.sum_range_add]
      have : ∑ x ∈ Finset.range p, (if ∃ s ∈ R, s ∣ t * p + x then 1 else 0)
          = ∑ x ∈ Finset.range p, (if ∃ s ∈ R, s ∣ x then 1 else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [hper x]
      rw [this, ih]
      ring

/-- Rescaling: the multiples of `d * R` below `W` correspond to the multiples of `R`
below `W / d`. -/
private lemma cnt_scale (R : Finset ℕ) {d W : ℕ} (hd : 0 < d) (hdW : d ∣ W) :
    ((Finset.range W).filter fun x => ∃ s ∈ R, d * s ∣ x).card = cnt R (W / d) := by
  classical
  have himg : (Finset.range W).filter (fun x => ∃ s ∈ R, d * s ∣ x)
      = ((Finset.range (W / d)).filter (fun y => ∃ s ∈ R, s ∣ y)).image (fun y => d * y) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hxW, s, hs, hdsx⟩
      have hdx : d ∣ x := (dvd_mul_right d s).trans hdsx
      refine ⟨x / d, ⟨?_, ?_⟩, Nat.mul_div_cancel' hdx⟩
      · have h1 : d * (x / d) < d * (W / d) := by
          rw [Nat.mul_div_cancel' hdx, Nat.mul_div_cancel' hdW]; exact hxW
        exact Nat.lt_of_mul_lt_mul_left h1
      · refine ⟨s, hs, ?_⟩
        have : d * s ∣ d * (x / d) := by rw [Nat.mul_div_cancel' hdx]; exact hdsx
        exact (Nat.mul_dvd_mul_iff_left hd).mp this
    · rintro ⟨y, ⟨hy, s, hs, hsy⟩, rfl⟩
      refine ⟨?_, s, hs, mul_dvd_mul_left d hsy⟩
      have : d * y < d * (W / d) := by exact (Nat.mul_lt_mul_left hd).mpr hy
      rwa [Nat.mul_div_cancel' hdW] at this
  rw [himg, Finset.card_image_of_injective _ (fun x y hxy => Nat.eq_of_mul_eq_mul_left hd hxy)]
  rfl

/-! ## Part 2 : the divisor injection -/

/-- **Key pointwise inequality.**  Let `R` be a finite set of positive integers, all divisible
by `gg` and all dividing `nn = gg * D`.  Then for every `x`, the number of members of `R`
dividing `x` is at most the number of divisors `d` of `D` such that `d * s ∣ x` for some
`s ∈ R`.

The injection is `s ↦ Y / s`, where `Y` is the lcm of the members of `R` dividing `x`:
indeed `Y ∣ x`, so `(Y / s) * s = Y ∣ x`, and `Y / s ∣ D` because `Y ∣ nn` and `gg ∣ s`. -/
private lemma card_filter_dvd_le {R : Finset ℕ} (hR : ∀ s ∈ R, 0 < s)
    {gg nn D : ℕ} (hg0 : 0 < gg) (hD0 : 0 < D) (hgs : ∀ s ∈ R, gg ∣ s)
    (hsn : ∀ s ∈ R, s ∣ nn) (hgD : gg * D = nn) (x : ℕ) :
    (R.filter fun s => s ∣ x).card
      ≤ (D.divisors.filter fun d => ∃ s ∈ R, d * s ∣ x).card := by
  classical
  set A := R.filter (fun s => s ∣ x) with hA
  set Y := A.lcm id with hYdef
  have hmem : ∀ s ∈ A, s ∈ R ∧ s ∣ x := by
    intro s hs; exact Finset.mem_filter.mp hs
  have hY0 : Y ≠ 0 := by
    intro h0
    rw [hYdef, Finset.lcm_eq_zero_iff] at h0
    obtain ⟨s, hs, hs0⟩ := h0
    exact absurd hs0 (hR s (hmem s hs).1).ne'
  have hYx : Y ∣ x := Finset.lcm_dvd (fun s hs => (hmem s hs).2)
  have hYn : Y ∣ nn := Finset.lcm_dvd (fun s hs => hsn s (hmem s hs).1)
  refine Finset.card_le_card_of_injOn (fun s => Y / s) ?_ ?_
  · intro s hs
    have hsA : s ∈ A := hs
    have hsR : s ∈ R := (hmem s hsA).1
    have hs0 : 0 < s := hR s hsR
    have hsY : s ∣ Y := Finset.dvd_lcm hsA
    obtain ⟨d, hd⟩ := hsY
    have hdiv : Y / s = d := by rw [hd, Nat.mul_div_cancel_left _ hs0]
    obtain ⟨s₁, hs₁⟩ := hgs s hsR
    have h1 : gg * (s₁ * d) ∣ gg * D := by
      rw [hgD]
      calc gg * (s₁ * d) = s * d := by rw [hs₁]; ring
        _ = Y := hd.symm
        _ ∣ nn := hYn
    have h2 : s₁ * d ∣ D := (Nat.mul_dvd_mul_iff_left hg0).mp h1
    simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors, hdiv]
    refine ⟨⟨(dvd_mul_left d s₁).trans h2, hD0.ne'⟩, s, hsR, ?_⟩
    calc d * s = s * d := by ring
      _ = Y := hd.symm
      _ ∣ x := hYx
  · intro s hs s' hs' hss'
    have h1 : Y / (Y / s) = s := Nat.div_div_self (Finset.dvd_lcm hs) hY0
    have h2 : Y / (Y / s') = s' := Nat.div_div_self (Finset.dvd_lcm hs') hY0
    rw [← h1, ← h2]
    simp only [hss']

/-- Aggregated form of `card_filter_dvd_le`: summing over `x < W`. -/
private lemma sum_div_le_sum_cnt {R : Finset ℕ} (hR : ∀ s ∈ R, 0 < s)
    {gg nn D W : ℕ} (hg0 : 0 < gg) (hD0 : 0 < D) (hgs : ∀ s ∈ R, gg ∣ s)
    (hsn : ∀ s ∈ R, s ∣ nn) (hgD : gg * D = nn)
    (hsW : ∀ s ∈ R, s ∣ W) (hDW : D ∣ W) :
    ∑ s ∈ R, W / s ≤ ∑ d ∈ D.divisors, cnt R (W / d) := by
  classical
  calc ∑ s ∈ R, W / s
      = ∑ s ∈ R, ((Finset.range W).filter fun x => s ∣ x).card := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [SunDev.card_filter_dvd_range (hsW s hs) (hR s hs).ne']
    _ = ∑ x ∈ Finset.range W, (R.filter fun s => s ∣ x).card :=
        double_count R (Finset.range W) (fun s x => s ∣ x)
    _ ≤ ∑ x ∈ Finset.range W, (D.divisors.filter fun d => ∃ s ∈ R, d * s ∣ x).card :=
        Finset.sum_le_sum fun x _ => card_filter_dvd_le hR hg0 hD0 hgs hsn hgD x
    _ = ∑ d ∈ D.divisors, ((Finset.range W).filter fun x => ∃ s ∈ R, d * s ∣ x).card :=
        double_count (Finset.range W) D.divisors (fun x d => ∃ s ∈ R, d * s ∣ x)
    _ = ∑ d ∈ D.divisors, cnt R (W / d) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdD : d ∣ D := (Nat.mem_divisors.mp hd).1
        exact cnt_scale R (Nat.pos_of_mem_divisors hd) (hdD.trans hDW)

/-! ## Part 3 : the arithmetic heart of Theorem 3.2 -/

/-- **The arithmetic content of Theorem 3.2.**  Write `n i` for the indices `[G : K i]`,
`hidx` for `[G : H]`, `m i` for the indices `[G : K i H]` (only the divisibilities
`m i ∣ hidx` and `m i ∣ n i` are used), `Q` for `[G : F]` with `F ≤ K i` for all `i`, and
`M` for a bound on the multiplicities of the values of `n`.  If the counting inequality
`hcount` (supplied by Theorem 3.1) holds, then
`[n 1, …, n k] ≤ M · (hidx, (n 1, …, n k)) · σ([n 1, …, n k] / (n 1, …, n k))`. -/
private lemma arith_main {k : ℕ} (hk : 0 < k) {n : Fin k → ℕ} (hn : ∀ i, 0 < n i)
    {hidx : ℕ} (hh : 0 < hidx) {m : Fin k → ℕ} (hmh : ∀ i, m i ∣ hidx)
    (hmn : ∀ i, m i ∣ n i) {Q : ℕ} (hQ : Q ≠ 0) (hnQ : ∀ i, n i ∣ Q)
    {M : ℕ} (hM : ∀ v, (Finset.univ.filter fun i => n i = v).card ≤ M)
    (hcount : ((Finset.range Q).filter fun x => ∃ i, m i ∣ x).card ≤ ∑ i, Q / n i) :
    Finset.univ.lcm n ≤ M * Nat.gcd hidx (Finset.univ.gcd n) *
      ∑ d ∈ ((Finset.univ.lcm n) / (Finset.univ.gcd n)).divisors, d := by
  classical
  set i₀ : Fin k := ⟨0, hk⟩ with hi₀
  set g := Finset.univ.gcd n with hgdef
  set L := Finset.univ.lcm n with hLdef
  have hgn : ∀ i, g ∣ n i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  have hnL : ∀ i, n i ∣ L := fun i => Finset.dvd_lcm (Finset.mem_univ i)
  have hg0 : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · exact absurd (Nat.eq_zero_of_zero_dvd (h0 ▸ hgn i₀)) (hn i₀).ne'
    · exact h0
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · exfalso
      rw [hLdef, Finset.lcm_eq_zero_iff] at h0
      obtain ⟨i, -, hi⟩ := h0
      exact absurd hi (hn i).ne'
    · exact h0
  have hgL : g ∣ L := (hgn i₀).trans (hnL i₀)
  set c := Nat.gcd hidx g with hcdef
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso; rw [hcdef, Nat.gcd_eq_zero_iff] at h0; exact absurd h0.1 hh.ne'
    · exact h0
  have hcg : c ∣ g := Nat.gcd_dvd_right hidx g
  set u := g / c with hudef
  have hcu : c * u = g := Nat.mul_div_cancel' hcg
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · exact absurd (by rw [← hcu, h0, mul_zero]) hg0.ne'
    · exact h0
  -- `lcm hidx g = hidx * u`
  have hlcm : Nat.lcm hidx g = hidx * u := by
    refine Nat.eq_of_mul_eq_mul_left hc0 ?_
    calc c * Nat.lcm hidx g = hidx * g := Nat.gcd_mul_lcm hidx g
      _ = c * (hidx * u) := by rw [← hcu]; ring
  -- the crucial divisibility `u * m i ∣ n i`
  have hkey : ∀ i, u * m i ∣ n i := by
    intro i
    have h1 : Nat.lcm hidx g ∣ Nat.lcm hidx (n i) :=
      Nat.lcm_dvd (Nat.dvd_lcm_left hidx (n i)) ((hgn i).trans (Nat.dvd_lcm_right hidx (n i)))
    have h2 : m i ∣ Nat.gcd hidx (n i) := Nat.dvd_gcd (hmh i) (hmn i)
    have h3 : Nat.lcm hidx g * m i ∣ Nat.lcm hidx (n i) * Nat.gcd hidx (n i) := mul_dvd_mul h1 h2
    have h4 : Nat.lcm hidx (n i) * Nat.gcd hidx (n i) = hidx * n i := by
      rw [mul_comm]; exact Nat.gcd_mul_lcm hidx (n i)
    rw [h4, hlcm] at h3
    exact (Nat.mul_dvd_mul_iff_left hh).mp (by rw [← mul_assoc]; exact h3)
  set r : Fin k → ℕ := fun i => n i / u with hrdef
  have hun : ∀ i, u ∣ n i := fun i => (dvd_mul_right u (m i)).trans (hkey i)
  have hur : ∀ i, u * r i = n i := fun i => Nat.mul_div_cancel' (hun i)
  have hr0 : ∀ i, 0 < r i := by
    intro i
    rcases Nat.eq_zero_or_pos (r i) with h0 | h0
    · exact absurd (by rw [← hur i, h0, mul_zero] : n i = 0) (hn i).ne'
    · exact h0
  have hmr : ∀ i, m i ∣ r i :=
    fun i => (Nat.mul_dvd_mul_iff_left hu0).mp (by rw [hur i]; exact hkey i)
  have hrn : ∀ i, r i ∣ n i := fun i => Dvd.intro_left u (hur i)
  have hrQ : ∀ i, r i ∣ Q := fun i => (hrn i).trans (hnQ i)
  set R := Finset.image r Finset.univ with hRdef
  have hRmem : ∀ {s : ℕ}, s ∈ R → ∃ i, r i = s := by
    intro s hs
    rw [hRdef, Finset.mem_image] at hs
    obtain ⟨i, -, hi⟩ := hs
    exact ⟨i, hi⟩
  have hRin : ∀ i, r i ∈ R := fun i => Finset.mem_image_of_mem r (Finset.mem_univ i)
  have hRpos : ∀ s ∈ R, 0 < s := by
    intro s hs; obtain ⟨i, rfl⟩ := hRmem hs; exact hr0 i
  -- the data for `sum_div_le_sum_cnt`
  set D := L / g with hDdef
  have hgD : g * D = L := Nat.mul_div_cancel' hgL
  have hD0 : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · exact absurd (by rw [← hgD, h0, mul_zero]) hL0.ne'
    · exact h0
  have huL : u ∣ L := (hun i₀).trans (hnL i₀)
  set N' := L / u with hN'def
  have huN' : u * N' = L := Nat.mul_div_cancel' huL
  have hgs : ∀ s ∈ R, c ∣ s := by
    intro s hs
    obtain ⟨i, rfl⟩ := hRmem hs
    refine (Nat.mul_dvd_mul_iff_left hu0).mp ?_
    calc u * c = c * u := by ring
      _ = g := hcu
      _ ∣ n i := hgn i
      _ = u * r i := (hur i).symm
  have hsn' : ∀ s ∈ R, s ∣ N' := by
    intro s hs
    obtain ⟨i, rfl⟩ := hRmem hs
    refine (Nat.mul_dvd_mul_iff_left hu0).mp ?_
    calc u * r i = n i := hur i
      _ ∣ L := hnL i
      _ = u * N' := huN'.symm
  have hgDN : c * D = N' := by
    refine Nat.eq_of_mul_eq_mul_left hu0 ?_
    calc u * (c * D) = g * D := by rw [← hcu]; ring
      _ = L := hgD
      _ = u * N' := huN'.symm
  set W := Q * D with hWdef
  have hsW : ∀ s ∈ R, s ∣ W := by
    intro s hs
    obtain ⟨i, rfl⟩ := hRmem hs
    exact (hrQ i).trans (Dvd.intro D rfl)
  have hDW : D ∣ W := Dvd.intro_left Q rfl
  -- the lower bound
  have hlower : ∑ s ∈ R, W / s ≤ ∑ d ∈ D.divisors, cnt R (W / d) :=
    sum_div_le_sum_cnt hRpos hc0 hD0 hgs hsn' hgDN hsW hDW
  -- evaluate the right-hand side
  have hRQ : ∀ s ∈ R, s ∣ Q := by
    intro s hs; obtain ⟨i, rfl⟩ := hRmem hs; exact hrQ i
  have hright : ∑ d ∈ D.divisors, cnt R (W / d) = (∑ d ∈ D.divisors, d) * cnt R Q := by
    have h1 : ∀ d ∈ D.divisors, cnt R (W / d) = (D / d) * cnt R Q := by
      intro d hd
      have hdD : d ∣ D := (Nat.mem_divisors.mp hd).1
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      obtain ⟨D', hD'⟩ := hdD
      have hWd : W / d = D' * Q := by
        have hWe : W = d * (D' * Q) := by rw [hWdef, hD']; ring
        rw [hWe, Nat.mul_div_cancel_left _ hd0]
      have hDd : D / d = D' := by rw [hD', Nat.mul_div_cancel_left _ hd0]
      rw [hWd, hDd]
      exact cnt_mul R hRQ D'
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
    congr 1
    exact Nat.sum_div_divisors D id
  -- evaluate the left-hand side
  set S := ∑ s ∈ R, Q / (u * s) with hSdef
  have huRQ : ∀ s ∈ R, u * s ∣ Q := by
    intro s hs; obtain ⟨i, rfl⟩ := hRmem hs; rw [hur i]; exact hnQ i
  have hleft : ∑ s ∈ R, W / s = u * D * S := by
    have h1 : ∀ s ∈ R, W / s = u * D * (Q / (u * s)) := by
      intro s hs
      obtain ⟨q, hq⟩ := huRQ s hs
      have hs0 : 0 < s := hRpos s hs
      have hus0 : 0 < u * s := Nat.mul_pos hu0 hs0
      have hQq : Q / (u * s) = q := by rw [hq, Nat.mul_div_cancel_left _ hus0]
      have hW : W = s * (u * D * q) := by rw [hWdef, hq]; ring
      rw [hQq, hW, Nat.mul_div_cancel_left _ hs0]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hSdef]
  -- the upper bound for `cnt R Q`
  have hupper : cnt R Q ≤ M * S := by
    have h1 : cnt R Q ≤ ((Finset.range Q).filter fun x => ∃ i, m i ∣ x).card := by
      refine Finset.card_le_card ?_
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      obtain ⟨hxQ, s, hs, hsx⟩ := hx
      obtain ⟨i, rfl⟩ := hRmem hs
      exact ⟨hxQ, i, (hmr i).trans hsx⟩
    have h2 : ∑ i, Q / n i ≤ M * S := by
      have h3 : ∑ i, Q / n i
          = ∑ s ∈ R, ∑ i ∈ Finset.univ.filter (fun i => r i = s), Q / n i :=
        (Finset.sum_fiberwise_of_maps_to (fun i _ => hRin i) _).symm
      have h4 : ∀ s ∈ R, ∑ i ∈ Finset.univ.filter (fun i => r i = s), Q / n i
          ≤ M * (Q / (u * s)) := by
        intro s hs
        have hfib : (Finset.univ.filter fun i => r i = s).card ≤ M := by
          have hsub : (Finset.univ.filter fun i => r i = s)
              ⊆ (Finset.univ.filter fun i => n i = u * s) := by
            intro i hi
            rw [Finset.mem_filter] at hi ⊢
            exact ⟨hi.1, by rw [← hur i, hi.2]⟩
          exact le_trans (Finset.card_le_card hsub) (hM (u * s))
        have h5 : ∀ i ∈ Finset.univ.filter (fun i => r i = s), Q / n i = Q / (u * s) := by
          intro i hi
          have : r i = s := (Finset.mem_filter.mp hi).2
          rw [← hur i, this]
        calc ∑ i ∈ Finset.univ.filter (fun i => r i = s), Q / n i
            = ∑ i ∈ Finset.univ.filter (fun i => r i = s), Q / (u * s) :=
              Finset.sum_congr rfl h5
          _ = (Finset.univ.filter fun i => r i = s).card * (Q / (u * s)) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ M * (Q / (u * s)) := Nat.mul_le_mul_right _ hfib
      calc ∑ i, Q / n i = ∑ s ∈ R, ∑ i ∈ Finset.univ.filter (fun i => r i = s), Q / n i := h3
        _ ≤ ∑ s ∈ R, M * (Q / (u * s)) := Finset.sum_le_sum h4
        _ = M * S := by rw [hSdef, Finset.mul_sum]
    exact le_trans (le_trans h1 hcount) h2
  -- combine
  have hS0 : 0 < S := by
    have h1 : 0 < Q / (u * r i₀) := by
      rw [hur i₀]
      exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) (hnQ i₀)) (hn i₀)
    exact lt_of_lt_of_le h1 (Finset.single_le_sum (f := fun s => Q / (u * s))
      (fun s _ => Nat.zero_le _) (hRin i₀))
  have hfinal : u * D ≤ (∑ d ∈ D.divisors, d) * M := by
    refine Nat.le_of_mul_le_mul_right ?_ hS0
    calc u * D * S = ∑ s ∈ R, W / s := hleft.symm
      _ ≤ ∑ d ∈ D.divisors, cnt R (W / d) := hlower
      _ = (∑ d ∈ D.divisors, d) * cnt R Q := hright
      _ ≤ (∑ d ∈ D.divisors, d) * (M * S) := Nat.mul_le_mul_left _ hupper
      _ = (∑ d ∈ D.divisors, d) * M * S := by ring
  calc L = c * (u * D) := by rw [← hgD, ← hcu]; ring
    _ ≤ c * ((∑ d ∈ D.divisors, d) * M) := Nat.mul_le_mul_left _ hfinal
    _ = M * c * ∑ d ∈ D.divisors, d := by ring

/-! ## Part 4 : group theory -/

section GroupTheory

variable {G : Type*} [Group G]

/-- If `K` is subnormal and `H` is normal, then `K ⊔ H` is subnormal: it is the preimage of
the (subnormal) image of `K` in `G ⧸ H`. -/
private lemma sup_isSubnormal (K H : Subgroup G) [H.Normal] (hK : K.IsSubnormal) :
    (K ⊔ H).IsSubnormal := by
  have h1 : (Subgroup.map (QuotientGroup.mk' H) K).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective H) hK
  have h2 := Subgroup.IsSubnormal.comap (QuotientGroup.mk' H) h1
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2

/-- The natural map `N ⧸ (F ∩ N) → G ⧸ F`, translated by `a`. -/
private def cosetMap (F N : Subgroup G) (a : G) : (↥N ⧸ (F.subgroupOf N)) → G ⧸ F := fun q =>
  Quotient.liftOn' q (fun x : ↥N => (QuotientGroup.mk (a * (x : G)) : G ⧸ F)) (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy
    have hx : ((x : G))⁻¹ * (y : G) ∈ F := by
      have := Subgroup.mem_subgroupOf.mp hxy
      push_cast at this
      exact this
    refine (QuotientGroup.eq (s := F)).mpr ?_
    have he : (a * (x : G))⁻¹ * (a * (y : G)) = ((x : G))⁻¹ * (y : G) := by group
    rw [he]; exact hx)

private lemma image_mk_smul_subset_range (F N : Subgroup G) (a : G) :
    (QuotientGroup.mk '' (a • (N : Set G)) : Set (G ⧸ F)) ⊆ Set.range (cosetMap F N a) := by
  rintro q ⟨x, hx, rfl⟩
  rw [Set.mem_smul_set] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨QuotientGroup.mk ⟨y, hy⟩, rfl⟩

/-- The coset `a • N` meets at most `[N : F ∩ N]` cosets of `F`. -/
private lemma ncard_image_smul_le_relIndex (F N : Subgroup G) (a : G)
    (hfin : F.relIndex N ≠ 0) :
    (QuotientGroup.mk '' (a • (N : Set G)) : Set (G ⧸ F)).ncard ≤ F.relIndex N := by
  have hcard : F.relIndex N = Nat.card (↥N ⧸ (F.subgroupOf N)) := Subgroup.index_eq_card _
  have hfinite : Finite (↥N ⧸ (F.subgroupOf N)) :=
    Nat.finite_of_card_ne_zero (by rw [← hcard]; exact hfin)
  calc (QuotientGroup.mk '' (a • (N : Set G)) : Set (G ⧸ F)).ncard
      ≤ (Set.range (cosetMap F N a)).ncard :=
        Set.ncard_le_ncard (image_mk_smul_subset_range F N a) (Set.finite_range _)
    _ ≤ Nat.card (↥N ⧸ (F.subgroupOf N)) := by
        rw [← Set.image_univ, ← Set.ncard_univ (↥N ⧸ (F.subgroupOf N))]
        exact Set.ncard_image_le Set.finite_univ
    _ = F.relIndex N := hcard.symm

end GroupTheory

/-! ## Part 5 : Theorem 3.2, case (a) -/

/-- **Sun, Theorem 3.2, case (a).**  Let `K 1, …, K k` be subnormal subgroups of finite index
of a group `G`, let `a 1, …, a k ∈ G`, and let `H` be a normal subgroup of finite index such
that `⋃ i, a i (K i)` is a union of left cosets of `H` (expressed here as closure under right
multiplication by `H`).  Let `M` bound the multiplicities of the indices `[G : K i]`.  Then,
writing `h = [G : H]`, `g = ([G : K 1], …, [G : K k])` and `L = [[G : K 1], …, [G : K k]]`,

`L ≤ M * (h, g) * σ (L / g)`.

Dividing by `(h, g) * (L / g)`, this is Sun's display (3.8):
`g / (h, g) ≤ M * ∑_{d ∣ L / g} 1 / d`. -/
theorem lcm_le_indexMultiplicity_mul_sigma {G : Type*} [Group G] {k : ℕ} (hk : 0 < k)
    (K : Fin k → Subgroup G) (a : Fin k → G) (H : Subgroup G) [H.Normal]
    (hHfin : H.index ≠ 0) (hKfin : ∀ i, (K i).index ≠ 0) (hsn : ∀ i, (K i).IsSubnormal)
    (hunion : ∀ x ∈ ⋃ i, (a i) • (K i : Set G), ∀ y ∈ H,
      x * y ∈ ⋃ i, (a i) • (K i : Set G))
    (M : ℕ) (hM : ∀ m, indexMultiplicity K m ≤ M) :
    coverLcm K ≤
      M * Nat.gcd H.index (Finset.univ.gcd fun i => (K i).index) *
        ∑ d ∈ (coverLcm K / Finset.univ.gcd fun i => (K i).index).divisors, d := by
  classical
  set F : Subgroup G := ⨅ i, K i with hFdef
  have hFK : ∀ i, F ≤ K i := fun i => iInf_le K i
  -- `F` has finite index (Lemma 2.1)
  have hprod : (∏ i, (K i).index) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hKfin i
  have hFdvd : F.index ∣ ∏ i, (K i).index :=
    SunDev.index_iInf_dvd_prod K hsn fun i => ⟨hKfin i⟩
  have hFfin : F.index ≠ 0 := fun h0 => hprod (Nat.eq_zero_of_zero_dvd (h0 ▸ hFdvd))
  have hFq : Finite (G ⧸ F) :=
    Nat.finite_of_card_ne_zero (by rw [← Subgroup.index_eq_card]; exact hFfin)
  -- the enlarged family `K i H`, still subnormal and containing `F`
  set Lg : Fin k → Subgroup G := fun i => K i ⊔ H with hLgdef
  have hLsn : ∀ i, (Lg i).IsSubnormal := fun i => sup_isSubnormal (K i) H (hsn i)
  have hFL : ∀ i, F ≤ Lg i := fun i => (hFK i).trans le_sup_left
  -- the union of the `a i (K i H)` is still the union of the `a i (K i)`
  have hUsub : (⋃ i, a i • (Lg i : Set G)) ⊆ ⋃ i, a i • (K i : Set G) := by
    rintro z hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨i, hzi⟩ := hz
    rw [Set.mem_smul_set] at hzi
    obtain ⟨y, hy, rfl⟩ := hzi
    have hy' : y ∈ (K i : Set G) * (H : Set G) := by
      rw [← Subgroup.mul_normal]; exact hy
    obtain ⟨κ, hκ, η, hη, rfl⟩ := hy'
    have h1 : a i * κ ∈ ⋃ j, a j • (K j : Set G) := Set.mem_iUnion.mpr ⟨i, ⟨κ, hκ, rfl⟩⟩
    have h2 := hunion _ h1 η hη
    have h3 : a i • (κ * η) = a i * κ * η := by
      simp [smul_eq_mul, mul_assoc]
    rw [h3]; exact h2
  -- Theorem 3.1
  have hT31 := SunT31_B.card_cosets_biUnion_ge F hFfin Lg hFL hLsn a
  have hrel : ∀ i, F.relIndex (K i) = F.index / (K i).index := by
    intro i
    have hmul := Subgroup.relIndex_mul_index (hFK i)
    rw [← hmul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (hKfin i))]
  have hrelfin : ∀ i, F.relIndex (K i) ≠ 0 := by
    intro i h0
    have hmul := Subgroup.relIndex_mul_index (hFK i)
    rw [h0, zero_mul] at hmul
    exact hFfin hmul.symm
  have hncard : ((QuotientGroup.mk '' (⋃ i, a i • (Lg i : Set G)) : Set (G ⧸ F))).ncard
      ≤ ∑ i, F.index / (K i).index := by
    calc ((QuotientGroup.mk '' (⋃ i, a i • (Lg i : Set G)) : Set (G ⧸ F))).ncard
        ≤ ((QuotientGroup.mk '' (⋃ i, a i • (K i : Set G)) : Set (G ⧸ F))).ncard :=
          Set.ncard_le_ncard (Set.image_mono hUsub) (Set.toFinite _)
      _ = (⋃ i, (QuotientGroup.mk '' (a i • (K i : Set G)) : Set (G ⧸ F))).ncard := by
          rw [Set.image_iUnion]
      _ ≤ ∑ i, ((QuotientGroup.mk '' (a i • (K i : Set G)) : Set (G ⧸ F))).ncard :=
          Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ i, F.relIndex (K i) :=
          Finset.sum_le_sum fun i _ => ncard_image_smul_le_relIndex F (K i) (a i) (hrelfin i)
      _ = ∑ i, F.index / (K i).index := Finset.sum_congr rfl fun i _ => hrel i
  have hcount : ((Finset.range F.index).filter fun x => ∃ i, (Lg i).index ∣ x).card
      ≤ ∑ i, F.index / (K i).index := le_trans hT31 hncard
  exact arith_main hk (n := fun i => (K i).index) (fun i => Nat.pos_of_ne_zero (hKfin i))
    (hidx := H.index) (Nat.pos_of_ne_zero hHfin) (m := fun i => (Lg i).index)
    (fun i => Subgroup.index_dvd_of_le le_sup_right)
    (fun i => Subgroup.index_dvd_of_le le_sup_left)
    (Q := F.index) hFfin (fun i => Subgroup.index_dvd_of_le (hFK i))
    (M := M) hM hcount

end SunT32_B

/-!
# A divisor-sum bound

`σ(m) · ∏_{p ∣ L} (p-1) < m · ∏_{p ∣ L} p` for `m ∣ L` and `L ≥ 2`, i.e.
`∑_{d ∣ m} 1/d < ∏_{p ∣ L} p/(p-1)`.  The divisors of `m` are a *finite* subfamily of the
`L`-factored numbers, whose reciprocals sum to the Euler product on the right; the inequality
is strict because `m · p` is `L`-factored for `p ∣ L` but is not a divisor of `m`.
-/

namespace SunSigma

open Nat

private noncomputable def rcp : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' a b := by push_cast; rw [mul_inv]

@[simp] private lemma rcp_apply (n : ℕ) : rcp n = (n : ℝ)⁻¹ := rfl

/-- The Euler product: the reciprocals of the `P`-factored numbers sum to `∏_{p ∈ P} p/(p-1)`. -/
private lemma hasSum_factored (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum ((Nat.factoredNumbers P).indicator fun n : ℕ => ((n : ℝ))⁻¹)
      (∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 1)) := by
  have h : ∀ {p : ℕ}, p.Prime → ‖rcp p‖ < 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have h0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hlt : (p : ℝ)⁻¹ < 1 := by
      have := (div_lt_one h0).mpr (show (1 : ℝ) < (p : ℝ) by linarith)
      simpa [one_div] using this
    rw [rcp_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hlt
  have H := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := rcp) h P).2
  rw [Finset.filter_true_of_mem hP] at H
  have hval : ∏ p ∈ P, (1 - rcp p)⁻¹ = ∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 1) := by
    refine Finset.prod_congr rfl fun p hpP => ?_
    have hp := hP p hpP
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [rcp_apply]
    field_simp
  rw [hval] at H
  rw [← hasSum_subtype_iff_indicator]
  exact H

/-- `∑_{d ∣ m} 1/d < ∏_{p ∣ L} p/(p-1)` whenever `m ∣ L` and `L ≥ 2`. -/
private lemma sum_inv_divisors_lt {m L : ℕ} (hm : m ≠ 0) (hmL : m ∣ L) (hL : 2 ≤ L) :
    ∑ d ∈ m.divisors, ((d : ℝ))⁻¹ < ∏ p ∈ L.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  classical
  set P := L.primeFactors with hPdef
  have hL0 : L ≠ 0 := by omega
  have hP : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hsum := hasSum_factored P hP
  set f : ℕ → ℝ := (Nat.factoredNumbers P).indicator fun n : ℕ => ((n : ℝ))⁻¹ with hf
  have hfnn : ∀ n, 0 ≤ f n := by
    intro n
    rw [hf]
    by_cases h : n ∈ Nat.factoredNumbers P
    · rw [Set.indicator_of_mem h]; positivity
    · rw [Set.indicator_of_notMem h]
  -- the prime factors of `m` lie in `P`
  have hmP : m.primeFactors ⊆ P := hPdef ▸ Nat.primeFactors_mono hmL hL0
  -- pick a prime of `L`
  obtain ⟨p₀, hp₀⟩ : P.Nonempty := by
    rw [hPdef, Nat.nonempty_primeFactors]
    omega
  have hp₀p : p₀.Prime := hP p₀ hp₀
  -- every divisor of `m` is `P`-factored, and `f` agrees with `d⁻¹` there
  have hdiv : ∀ d ∈ m.divisors, f d = ((d : ℝ))⁻¹ := by
    intro d hd
    obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
    have hd0 : d ≠ 0 := fun h => hm (Nat.eq_zero_of_zero_dvd (h ▸ hdm))
    have : d ∈ Nat.factoredNumbers P :=
      Nat.mem_factoredNumbers_of_primeFactors_subset hd0
        (le_trans (Nat.primeFactors_mono hdm hm) hmP)
    rw [hf, Set.indicator_of_mem this]
  -- `m * p₀` is `P`-factored but not a divisor of `m`
  have hmp₀ : m * p₀ ∈ Nat.factoredNumbers P := by
    refine Nat.mem_factoredNumbers_of_primeFactors_subset (Nat.mul_ne_zero hm hp₀p.ne_zero) ?_
    rw [Nat.primeFactors_mul hm hp₀p.ne_zero]
    exact Finset.union_subset hmP (by simpa [hp₀p.primeFactors] using hp₀)
  have hnotdvd : m * p₀ ∉ m.divisors := by
    intro h
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd
    have h2 : 2 ≤ p₀ := hp₀p.two_le
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    nlinarith
  -- compare the finite sum over `insert (m*p₀) m.divisors` with the total
  have hle := sum_le_hasSum (insert (m * p₀) m.divisors) (fun i _ => hfnn i) hsum
  rw [Finset.sum_insert hnotdvd, hf, Set.indicator_of_mem hmp₀] at hle
  have hrw : ∑ d ∈ m.divisors, f d = ∑ d ∈ m.divisors, ((d : ℝ))⁻¹ :=
    Finset.sum_congr rfl hdiv
  rw [hrw] at hle
  have hpos : (0 : ℝ) < ((m * p₀ : ℕ) : ℝ)⁻¹ := by
    have : 0 < ((m * p₀ : ℕ) : ℝ) := by
      have : 0 < m * p₀ := Nat.mul_pos (Nat.pos_of_ne_zero hm) hp₀p.pos
      exact_mod_cast this
    positivity
  linarith

/-- **The divisor-sum bound, in `ℕ`.** -/
theorem sigma_mul_prod_pred_lt {m L : ℕ} (hm : m ≠ 0) (hmL : m ∣ L) (hL : 2 ≤ L) :
    (∑ d ∈ m.divisors, d) * ∏ p ∈ L.primeFactors, (p - 1)
      < m * ∏ p ∈ L.primeFactors, p := by
  classical
  have hkey := sum_inv_divisors_lt hm hmL hL
  have hP : ∀ p ∈ L.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  -- clear denominators
  have hcast : ((∏ p ∈ L.primeFactors, (p - 1) : ℕ) : ℝ)
      = ∏ p ∈ L.primeFactors, ((p : ℝ) - 1) := by
    push_cast [Nat.cast_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have := (hP p hp).two_le
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hprodpos : (0 : ℝ) < ∏ p ∈ L.primeFactors, ((p : ℝ) - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (hP p hp).two_le
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast this
    linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := Nat.pos_of_ne_zero hm
    exact_mod_cast this
  -- `∑_{d ∣ m} d = m * ∑_{d ∣ m} 1/d`
  have hsigma : ((∑ d ∈ m.divisors, d : ℕ) : ℝ) = (m : ℝ) * ∑ d ∈ m.divisors, ((d : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    push_cast
    rw [← Nat.sum_div_divisors m (fun d => (d : ℝ))]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
    have hd0 : d ≠ 0 := fun h => hm (Nat.eq_zero_of_zero_dvd (h ▸ hdm))
    have hdR : ((d : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    rw [Nat.cast_div hdm hdR]
    field_simp
  -- combine
  have hprodeq : (∏ p ∈ L.primeFactors, (p : ℝ) / ((p : ℝ) - 1))
      * ∏ p ∈ L.primeFactors, ((p : ℝ) - 1) = ∏ p ∈ L.primeFactors, (p : ℝ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have h2 := (hP p hp).two_le
    have h2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
    have hne : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  have hfinal : ((∑ d ∈ m.divisors, d : ℕ) : ℝ) * ((∏ p ∈ L.primeFactors, (p - 1) : ℕ) : ℝ)
      < ((m : ℕ) : ℝ) * ((∏ p ∈ L.primeFactors, p : ℕ) : ℝ) := by
    rw [hsigma, hcast, Nat.cast_prod]
    calc (m : ℝ) * (∑ d ∈ m.divisors, ((d : ℝ))⁻¹) * ∏ p ∈ L.primeFactors, ((p : ℝ) - 1)
        < (m : ℝ) * (∏ p ∈ L.primeFactors, (p : ℝ) / ((p : ℝ) - 1))
            * ∏ p ∈ L.primeFactors, ((p : ℝ) - 1) := by
          have h1 := mul_lt_mul_of_pos_left hkey hmpos
          exact mul_lt_mul_of_pos_right h1 hprodpos
      _ = (m : ℝ) * ∏ p ∈ L.primeFactors, (p : ℝ) := by rw [mul_assoc, hprodeq]
  exact_mod_cast hfinal

end SunSigma

namespace BArith
open BFFPyramidal

private lemma prod_primeFactors_pos (L : ℕ) : 0 < ∏ q ∈ L.primeFactors, q :=
  Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos

/-- The arithmetic core turning (3.8) for the subfamily into the Burshtein inequality. -/
theorem burshtein_arith {L L' g' m' h' M p : ℕ} (hL2 : 2 ≤ L)
    (hm'L : m' ∣ L) (hm'0 : m' ≠ 0) (hg'0 : g' ≠ 0)
    (hL'eq : L' = g' * m')
    (hdvd : p * Nat.gcd h' g' ∣ g') (hgcd0 : Nat.gcd h' g' ≠ 0) (hM1 : 1 ≤ M)
    (hineq : L' ≤ M * Nat.gcd h' g' * (∑ d ∈ m'.divisors, d)) :
    p * ∏ q ∈ L.primeFactors, (q - 1) < M * ∏ q ∈ L.primeFactors, q := by
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hg'0 hc
  have hgpos : 0 < Nat.gcd h' g' := Nat.pos_of_ne_zero hgcd0
  have hm'pos : 0 < m' := Nat.pos_of_ne_zero hm'0
  -- cancel the gcd from (3.8)
  have hstep : p * c * m' ≤ M * (∑ d ∈ m'.divisors, d) := by
    have h1 : Nat.gcd h' g' * (p * c * m') ≤ Nat.gcd h' g' * (M * (∑ d ∈ m'.divisors, d)) := by
      calc Nat.gcd h' g' * (p * c * m') = (p * Nat.gcd h' g' * c) * m' := by ring
        _ = g' * m' := by rw [← hc]
        _ = L' := hL'eq.symm
        _ ≤ M * Nat.gcd h' g' * (∑ d ∈ m'.divisors, d) := hineq
        _ = Nat.gcd h' g' * (M * (∑ d ∈ m'.divisors, d)) := by ring
    exact Nat.le_of_mul_le_mul_left h1 hgpos
  -- weaken `p * c` to `p`
  have hstep2 : p * m' ≤ M * (∑ d ∈ m'.divisors, d) := by
    refine le_trans ?_ hstep
    have : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
    calc p * m' = p * 1 * m' := by ring
      _ ≤ p * c * m' := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
  -- multiply by ∏ (q-1) and use the divisor-sum bound
  have hsig := SunSigma.sigma_mul_prod_pred_lt hm'0 hm'L hL2
  have hchain : p * m' * ∏ q ∈ L.primeFactors, (q - 1) < M * (m' * ∏ q ∈ L.primeFactors, q) := by
    calc p * m' * ∏ q ∈ L.primeFactors, (q - 1)
        ≤ M * (∑ d ∈ m'.divisors, d) * ∏ q ∈ L.primeFactors, (q - 1) :=
          Nat.mul_le_mul_right _ hstep2
      _ = M * ((∑ d ∈ m'.divisors, d) * ∏ q ∈ L.primeFactors, (q - 1)) := by ring
      _ < M * (m' * ∏ q ∈ L.primeFactors, q) :=
          Nat.mul_lt_mul_of_pos_left hsig (by omega)
  -- cancel `m'`
  have : m' * (p * ∏ q ∈ L.primeFactors, (q - 1)) < m' * (M * ∏ q ∈ L.primeFactors, q) := by
    calc m' * (p * ∏ q ∈ L.primeFactors, (q - 1))
        = p * m' * ∏ q ∈ L.primeFactors, (q - 1) := by ring
      _ < M * (m' * ∏ q ∈ L.primeFactors, q) := hchain
      _ = m' * (M * ∏ q ∈ L.primeFactors, q) := by ring
  exact Nat.lt_of_mul_lt_mul_left this

/-- From the Burshtein inequality to Theorem 4.3(i). -/
theorem minFac_le_of_burshtein {L M : ℕ} (hL2 : 2 ≤ L)
    (h : maxPrimeFac L * ∏ q ∈ L.primeFactors, (q - 1) < M * ∏ q ∈ L.primeFactors, q) :
    Nat.minFac L ≤ M := by
  have h1 := SunDev.minFac_pred_mul_prod_le hL2
  have hpos := prod_primeFactors_pos L
  have h2 : (Nat.minFac L - 1) * ∏ q ∈ L.primeFactors, q < M * ∏ q ∈ L.primeFactors, q :=
    lt_of_le_of_lt h1 h
  have h3 : Nat.minFac L - 1 < M := Nat.lt_of_mul_lt_mul_right h2
  have h4 : 2 ≤ Nat.minFac L := (Nat.minFac_prime (by omega : L ≠ 1)).two_le
  omega

end BArith

namespace SunBridge
open SubnormalCover BFFPyramidal Pointwise

/-- **Steps 3-4 of Theorem 4.1.**  For any set `J` of indices there is a normal subgroup `H` of
finite index, contained in every `K j` with `j ∈ J`, whose index has no prime divisor beyond the
primes of the indices `[G : K j]`, `j ∈ J`.  Take `H = ⨅_{j ∈ J} (K j)_G`; finiteness of the index
is Lemma 2.1 and the control on primes is Lemma 2.2. -/
theorem exists_normal_avoiding {G : Type*} [Group G] {k : ℕ} (K : Fin k → Subgroup G)
    (hfin : ∀ i, (K i).FiniteIndex) (hsn : ∀ i, (K i).IsSubnormal) (J : Finset (Fin k)) :
    ∃ H : Subgroup G, H.Normal ∧ H.index ≠ 0 ∧ (∀ j ∈ J, H ≤ K j) ∧
      ∀ q : ℕ, q.Prime → q ∣ H.index → ∃ j ∈ J, q ∣ (K j).index := by
  classical
  refine ⟨⨅ j ∈ J, (K j).normalCore, ?_, ?_, ?_, ?_⟩
  · -- normal
    refine Subgroup.normal_iInf_normal fun j => ?_
    refine Subgroup.normal_iInf_normal fun _ => ?_
    exact (K j).normalCore_normal
  · -- finite index, via Lemma 2.1
    have hsub : ∀ j ∈ J, ((K j).normalCore).IsSubnormal :=
      fun j _ => (K j).normalCore_normal.isSubnormal
    have hdvd := SunDev.index_iInf_dvd_prod_finset J (fun j => (K j).normalCore) hsub
    have hprod : (∏ j ∈ J, ((K j).normalCore).index) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
      haveI := hfin j
      exact (Subgroup.finiteIndex_normalCore (K j)).index_ne_zero
    intro h
    rw [h] at hdvd
    exact hprod (Nat.eq_zero_of_zero_dvd hdvd)
  · -- contained in each `K j`, `j ∈ J`
    intro j hj
    exact le_trans (le_trans (iInf_le _ j) (iInf_le _ hj)) (K j).normalCore_le
  · -- prime control, via Lemma 2.2
    intro q hq hqdvd
    have hsub : ∀ j ∈ J, ((K j).normalCore).IsSubnormal :=
      fun j _ => (K j).normalCore_normal.isSubnormal
    have hdvd := SunDev.index_iInf_dvd_prod_finset J (fun j => (K j).normalCore) hsub
    have hqprod : q ∣ ∏ j ∈ J, ((K j).normalCore).index := hqdvd.trans hdvd
    obtain ⟨j, hj, hqj⟩ := (Nat.Prime.prime hq).exists_mem_finset_dvd hqprod
    refine ⟨j, hj, ?_⟩
    haveI := hfin j
    have hcore0 : ((K j).normalCore).index ≠ 0 :=
      (Subgroup.finiteIndex_normalCore (K j)).index_ne_zero
    have hmem : q ∈ ((K j).normalCore).index.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqj, hcore0⟩
    rw [SunDev.primeFactors_normalCore_index (K j) (hsn j) (hfin j)] at hmem
    exact Nat.dvd_of_mem_primeFactors hmem

end SunBridge

namespace SunAux
open SubnormalCover BFFPyramidal Pointwise

variable {G : Type*} [Group G] {k : ℕ}

open scoped Classical in
private lemma card_filter_eq (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ)
    (hcov : IsUniformCover K a w) (x : G) :
    (Finset.univ.filter fun i => (a i)⁻¹ * x ∈ K i).card = w := by
  have h := hcov x
  rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at h

/-- A nontrivial uniform cover has at least two parts. -/
theorem two_le_of_isUniformCover (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ)
    (hcov : IsUniformCover K a w) (hnt : ∃ i, K i ≠ ⊤) : 2 ≤ k := by
  classical
  obtain ⟨i0, hi0⟩ := hnt
  by_contra hk
  have hkpos : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact i0.elim0)
  have hk1 : k = 1 := by omega
  haveI hss : Subsingleton (Fin k) := by subst hk1; infer_instance
  obtain ⟨u, hu⟩ : ∃ u : G, u ∉ K i0 := by
    by_contra h
    push Not at h
    exact hi0 (le_antisymm le_top fun x _ => h x)
  have huniv : (Finset.univ : Finset (Fin k)) = {i0} := by
    ext i; simp [Subsingleton.elim i i0]
  -- at `a i0` the count is 1
  have e1 := card_filter_eq K a w hcov (a i0)
  rw [huniv] at e1
  have hmem1 : (a i0)⁻¹ * (a i0) ∈ K i0 := by simpa using (K i0).one_mem
  rw [Finset.filter_singleton, if_pos hmem1, Finset.card_singleton] at e1
  -- at `a i0 * u` the count is 0
  have e0 := card_filter_eq K a w hcov (a i0 * u)
  rw [huniv] at e0
  have hmem0 : (a i0)⁻¹ * (a i0 * u) ∉ K i0 := by
    have hrw : (a i0)⁻¹ * (a i0 * u) = u := by group
    rwa [hrw]
  rw [Finset.filter_singleton, if_neg hmem0, Finset.card_empty] at e0
  omega

/-- A nontrivial uniform cover of finite-index subgroups has modulus at least `2`. -/
theorem two_le_coverLcm (K : Fin k → Subgroup G)
    (hfin : ∀ i, (K i).FiniteIndex) (hnt : ∃ i, K i ≠ ⊤) : 2 ≤ coverLcm K := by
  classical
  obtain ⟨i0, hi0⟩ := hnt
  have h2 : 2 ≤ (K i0).index := by
    have hne0 : (K i0).index ≠ 0 := (hfin i0).index_ne_zero
    have hne1 : (K i0).index ≠ 1 := fun h => hi0 (Subgroup.index_eq_one.mp h)
    omega
  have hdvd : (K i0).index ∣ coverLcm K := Finset.dvd_lcm (Finset.mem_univ i0)
  have hL0 : coverLcm K ≠ 0 := by
    intro h
    rw [coverLcm, Finset.lcm_eq_zero_iff] at h
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and] at h
    obtain ⟨i, hi⟩ := h
    exact (hfin i).index_ne_zero hi
  exact le_trans h2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hdvd)

/-- The Herzog-Schönheim corollary, given the goal theorem. -/
theorem herzog_schonheim_of_multiplicity
    (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ) (hcov : IsUniformCover K a w)
    (hfin : ∀ i, (K i).FiniteIndex) (hnt : ∃ i, K i ≠ ⊤)
    (hgoal : ∃ j : Fin k, maxPrimeFac (coverLcm K) ∣ (K j).index ∧
      Nat.minFac (coverLcm K) ≤ indexMultiplicity K ((K j).index)) :
    ∃ i j : Fin k, i ≠ j ∧ (K i).index = (K j).index := by
  classical
  obtain ⟨j, -, hmult⟩ := hgoal
  have h2L : 2 ≤ coverLcm K := two_le_coverLcm K hfin hnt
  have h2 : 2 ≤ Nat.minFac (coverLcm K) :=
    (Nat.minFac_prime (by omega : coverLcm K ≠ 1)).two_le
  have hcard : 1 < (Finset.univ.filter fun i => (K i).index = (K j).index).card := by
    have hge : 2 ≤ indexMultiplicity K ((K j).index) := le_trans h2 hmult
    rw [indexMultiplicity] at hge
    omega
  obtain ⟨i1, hi1, i2, hi2, hne⟩ := Finset.one_lt_card.mp hcard
  exact ⟨i1, i2, hne, by rw [(Finset.mem_filter.mp hi1).2, (Finset.mem_filter.mp hi2).2]⟩

end SunAux

namespace SunB2
open SubnormalCover BFFPyramidal Pointwise

private lemma maxPrimeFac_mem {L : ℕ} (h : 2 ≤ L) : maxPrimeFac L ∈ L.primeFactors := by
  have hne : L.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_sup L.primeFactors hne id
  rw [maxPrimeFac, hbeq]
  exact hb

private lemma exists_dvd_of_prime_dvd_lcm {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    {p : ℕ} (hp : p.Prime) (h : p ∣ s.lcm f) : ∃ i ∈ s, p ∣ f i := by
  induction s using Finset.induction_on with
  | empty => simp at h; exact absurd h hp.one_lt.ne'
  | insert a s ha ih =>
    rw [Finset.lcm_insert] at h
    rcases (Nat.Prime.dvd_mul hp).mp (h.trans (Nat.lcm_dvd_mul _ _)) with h1 | h1
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨i, hi, hpi⟩ := ih h1
      exact ⟨i, Finset.mem_insert_of_mem hi, hpi⟩

variable {G : Type*} [Group G] {k : ℕ}

/-- Theorem 3.2 (case (a)) as a hypothesis, so that the rest of Theorem 4.1 can be proved
independently of it. -/
def T32 (G : Type*) [Group G] : Prop :=
  ∀ {t : ℕ}, 0 < t → ∀ (L : Fin t → Subgroup G) (b : Fin t → G) (H : Subgroup G), H.Normal →
    H.index ≠ 0 → (∀ i, (L i).index ≠ 0) → (∀ i, (L i).IsSubnormal) →
    (∀ x ∈ ⋃ i, (b i) • (L i : Set G), ∀ y ∈ H, x * y ∈ ⋃ i, (b i) • (L i : Set G)) →
    ∀ M : ℕ, (∀ m, indexMultiplicity L m ≤ M) →
    coverLcm L ≤ M * Nat.gcd H.index (Finset.univ.gcd fun i => (L i).index)
      * ∑ d ∈ (coverLcm L / Finset.univ.gcd fun i => (L i).index).divisors, d

/-- **Theorem 4.1 (Burshtein inequality) modulo Theorem 3.2.** -/
theorem burshtein_inequality_of (hT32 : T32 G)
    (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ) (hcov : IsUniformCover K a w)
    (hfin : ∀ i, (K i).FiniteIndex) (hsn : ∀ i, (K i).IsSubnormal) (hnt : ∃ i, K i ≠ ⊤) :
    ∃ j : Fin k, maxPrimeFac (coverLcm K) ∣ (K j).index ∧
      maxPrimeFac (coverLcm K) * ∏ q ∈ (coverLcm K).primeFactors, (q - 1)
        < indexMultiplicity K ((K j).index) * ∏ q ∈ (coverLcm K).primeFactors, q := by
  classical
  set L := coverLcm K with hLdef
  have hL2 : 2 ≤ L := SunAux.two_le_coverLcm K hfin hnt
  set p := maxPrimeFac L with hpdef
  have hpmem : p ∈ L.primeFactors := maxPrimeFac_mem hL2
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpL : p ∣ L := Nat.dvd_of_mem_primeFactors hpmem
  have hn0 : ∀ i, (K i).index ≠ 0 := fun i => (hfin i).index_ne_zero
  -- the index set `I`
  set I : Finset (Fin k) := Finset.univ.filter (fun i => p ∣ (K i).index) with hIdef
  have hInonempty : I.Nonempty := by
    have hunf : coverLcm K = Finset.univ.lcm (fun i => (K i).index) := rfl
    have hpL' : p ∣ Finset.univ.lcm (fun i => (K i).index) := by
      rw [← hunf, ← hLdef]; exact hpL
    obtain ⟨i, -, hpi⟩ := exists_dvd_of_prime_dvd_lcm Finset.univ (fun i => (K i).index) hp hpL'
    exact ⟨i, by simp [hIdef, hpi]⟩
  have hImem : ∀ i, i ∈ I ↔ p ∣ (K i).index := by
    intro i; simp [hIdef]
  -- the normal subgroup `H` avoiding `p`
  obtain ⟨H, hHnorm, hH0, hHle, hHprimes⟩ :=
    SunBridge.exists_normal_avoiding K hfin hsn (Iᶜ : Finset (Fin k))
  have hpH : ¬ p ∣ H.index := by
    intro hpd
    obtain ⟨j, hj, hpj⟩ := hHprimes p hp hpd
    exact (Finset.mem_compl.mp hj) ((hImem j).mpr hpj)
  -- re-index the subfamily by `Fin I.card`
  set t := I.card with htdef
  have ht0 : 0 < t := Finset.card_pos.mpr hInonempty
  set e := I.equivFin with hedef
  set K' : Fin t → Subgroup G := fun j => K ((e.symm j : Fin k)) with hK'def
  set a' : Fin t → G := fun j => a ((e.symm j : Fin k)) with ha'def
  have hmemI : ∀ j : Fin t, ((e.symm j : Fin k)) ∈ I := fun j => (e.symm j).2
  -- the union over the subfamily
  have hUeq : (⋃ j, (a' j) • (K' j : Set G)) = ⋃ i ∈ (I : Set (Fin k)), (a i) • (K i : Set G) := by
    ext x
    simp only [Set.mem_iUnion, exists_prop, hK'def, ha'def]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨(e.symm j : Fin k), hmemI j, hj⟩
    · rintro ⟨i, hiI, hx⟩
      exact ⟨e ⟨i, hiI⟩, by rw [Equiv.symm_apply_apply]; exact hx⟩
  -- `hunion` for the subfamily and `H`
  have hunion : ∀ x ∈ ⋃ j, (a' j) • (K' j : Set G), ∀ y ∈ H,
      x * y ∈ ⋃ j, (a' j) • (K' j : Set G) := by
    intro x hx y hy
    rw [hUeq] at hx ⊢
    refine SunDev.isUniformCover_mul_mem_biUnion K a w hcov (I : Set (Fin k)) hx ?_
    refine Subgroup.mem_iInf.mpr fun j => Subgroup.mem_iInf.mpr fun hj => ?_
    exact hHle j (Finset.mem_compl.mpr hj) hy
  -- the multiplicity bound `M`
  obtain ⟨j₀, hj₀I, hj₀max⟩ :=
    I.exists_max_image (fun i => indexMultiplicity K ((K i).index)) hInonempty
  set M := indexMultiplicity K ((K j₀).index) with hMdef
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    simp only [indexMultiplicity]
    refine Finset.card_pos.mpr ⟨j₀, ?_⟩
    simp
  have hMbound : ∀ m, indexMultiplicity K' m ≤ M := by
    intro m
    rcases Finset.eq_empty_or_nonempty
      ((Finset.univ : Finset (Fin t)).filter fun j => (K' j).index = m) with hemp | ⟨j, hj⟩
    · simp only [indexMultiplicity, hemp, Finset.card_empty]; exact Nat.zero_le M
    · -- `m` is attained inside `I`, and then the two counts agree
      obtain ⟨-, hjm⟩ := Finset.mem_filter.mp hj
      have hi0 : ((e.symm j : Fin k)) ∈ I := hmemI j
      have hpm : p ∣ m := by rw [← hjm]; exact (hImem _).mp hi0
      have hcount : indexMultiplicity K' m ≤ indexMultiplicity K m := by
        simp only [indexMultiplicity]
        refine Finset.card_le_card_of_injOn (fun j => (e.symm j : Fin k)) ?_ ?_
        · intro j hj'
          obtain ⟨-, hjm'⟩ := Finset.mem_filter.mp hj'
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjm'⟩
        · intro x _ y _ hxy
          have hs : e.symm x = e.symm y := Subtype.ext hxy
          simpa using congrArg e hs
      refine le_trans hcount ?_
      -- every index equal to `m` is divisible by `p`, hence lies in `I`
      have hmm : indexMultiplicity K m ≤ M := by
        have hmI : m = (K ((e.symm j : Fin k))).index := hjm.symm
        rw [hMdef]
        have := hj₀max ((e.symm j : Fin k)) hi0
        rw [← hmI] at this
        exact this
      exact hmm
  -- apply Theorem 3.2
  set g' := Finset.univ.gcd (fun j : Fin t => (K' j).index) with hg'def
  have hn0' : ∀ j : Fin t, (K' j).index ≠ 0 := fun j => hn0 _
  have hg'0 : g' ≠ 0 := by
    rw [hg'def]
    intro h
    obtain ⟨j⟩ : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht0
    have : (K' j).index = 0 := Nat.eq_zero_of_zero_dvd (h ▸ Finset.gcd_dvd (Finset.mem_univ j))
    exact hn0' j this
  have hT := hT32 ht0 K' a' H hHnorm hH0 hn0' (fun j => hsn _) hunion M hMbound
  -- arithmetic: unwind the conclusion
  set L' := coverLcm K' with hL'def
  have hgL' : g' ∣ L' := by
    obtain ⟨j⟩ : Nonempty (Fin t) := Fin.pos_iff_nonempty.mp ht0
    exact dvd_trans (Finset.gcd_dvd (Finset.mem_univ j)) (Finset.dvd_lcm (Finset.mem_univ j))
  set m' := L' / g' with hm'def
  have hL'eq : L' = g' * m' := (Nat.mul_div_cancel' hgL').symm
  have hL'L : L' ∣ L := by
    rw [hL'def, hLdef, coverLcm, coverLcm]
    refine Finset.lcm_dvd fun j _ => ?_
    exact Finset.dvd_lcm (Finset.mem_univ _)
  have hm'L : m' ∣ L := dvd_trans ⟨g', by rw [hL'eq]; ring⟩ hL'L
  have hL'0 : L' ≠ 0 := fun h => by
    rw [h] at hL'L; exact (by omega : L ≠ 0) (Nat.eq_zero_of_zero_dvd hL'L)
  have hm'0 : m' ≠ 0 := by
    intro h; rw [h, mul_zero] at hL'eq; exact hL'0 hL'eq
  -- `p * gcd (H.index) g' ∣ g'`
  have hpg' : p ∣ g' := by
    rw [hg'def]
    refine Finset.dvd_gcd fun j _ => ?_
    exact (hImem _).mp (hmemI j)
  have hdgcd : Nat.gcd H.index g' ∣ g' := Nat.gcd_dvd_right _ _
  have hpnd : ¬ p ∣ Nat.gcd H.index g' := fun h => hpH (h.trans (Nat.gcd_dvd_left _ _))
  have hcop : Nat.Coprime p (Nat.gcd H.index g') := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpnd
  have hpdvd : p * Nat.gcd H.index g' ∣ g' := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpg' hdgcd
  have hgcd0 : Nat.gcd H.index g' ≠ 0 := fun h => hg'0 (Nat.eq_zero_of_gcd_eq_zero_right h)
  refine ⟨j₀, (hImem j₀).mp hj₀I, ?_⟩
  exact BArith.burshtein_arith hL2 hm'L hm'0 hg'0 hL'eq hpdvd hgcd0 hM1 hT

/-- **Theorem 4.3(i) modulo Theorem 3.2.** -/
theorem multiplicity_ge_minFac_of (hT32 : T32 G)
    (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ) (hcov : IsUniformCover K a w)
    (hfin : ∀ i, (K i).FiniteIndex) (hsn : ∀ i, (K i).IsSubnormal) (hnt : ∃ i, K i ≠ ⊤) :
    ∃ j : Fin k, maxPrimeFac (coverLcm K) ∣ (K j).index ∧
      Nat.minFac (coverLcm K) ≤ indexMultiplicity K ((K j).index) := by
  obtain ⟨j, hjd, hjlt⟩ := burshtein_inequality_of hT32 K a w hcov hfin hsn hnt
  exact ⟨j, hjd, BArith.minFac_le_of_burshtein (SunAux.two_le_coverLcm K hfin hnt) hjlt⟩

/-- **Herzog-Schönheim for subnormal uniform covers, modulo Theorem 3.2.** -/
theorem herzog_schonheim_subnormal_of (hT32 : T32 G)
    (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ) (hcov : IsUniformCover K a w)
    (hfin : ∀ i, (K i).FiniteIndex) (hsn : ∀ i, (K i).IsSubnormal) (hnt : ∃ i, K i ≠ ⊤) :
    ∃ i j : Fin k, i ≠ j ∧ (K i).index = (K j).index :=
  SunAux.herzog_schonheim_of_multiplicity K a w hcov hfin hnt
    (multiplicity_ge_minFac_of hT32 K a w hcov hfin hsn hnt)

end SunB2

private theorem T32_holds_local {G : Type*} [Group G] : SunB2.T32 G := by
  intro t ht L b H hHnorm hH0 hn0 hsn hunion M hM
  haveI := hHnorm
  exact SunT32_B.lcm_le_indexMultiplicity_mul_sigma ht L b H hH0 hn0 hsn hunion M hM

theorem solution {G : Type*} [Group G] {k : ℕ}
    (K : Fin k → Subgroup G) (a : Fin k → G) (w : ℕ) (hcov : IsUniformCover K a w)
    (hfin : ∀ i, (K i).FiniteIndex) (hsn : ∀ i, (K i).IsSubnormal) (hnt : ∃ i, K i ≠ ⊤) :
    ∃ j : Fin k, maxPrimeFac (coverLcm K) ∣ (K j).index ∧
      Nat.minFac (coverLcm K) ≤ indexMultiplicity K ((K j).index) :=
  SunB2.multiplicity_ge_minFac_of T32_holds_local K a w hcov hfin hsn hnt
