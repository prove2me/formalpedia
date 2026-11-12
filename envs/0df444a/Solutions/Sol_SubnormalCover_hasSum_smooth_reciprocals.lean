-- Prove2me | solution 1 for SubnormalCover.hasSum_smooth_reciprocals
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-14T13:05:26.905834+00:00
-- url     : https://prove2.me/submissions/21c69b91-8111-4001-8007-f1ec9937eb3b

import Mathlib
import Definitions.Def_SubnormalCover_uniformCover
import Definitions.Def_BFFPyramidal_arithmetic

/-!
# Lemma 3.4 — density of a union of progressions as an Euler product

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
# Sun, Lemma 3.4 (Variant A)

For positive integers `n 1, …, n k` all dividing `N` and all supported on a finite set `P`
of primes, the sum of `1/m` over the `P`-smooth multiples `m` of some `n i` equals the
density `|{x < N : ∃ i, n i ∣ x}| / N` times the Euler factor `∏_{p ∈ P} p/(p-1)`.

The proof is by inclusion–exclusion: pointwise, for every `m`,
`[∃ i, n i ∣ m] = 1 - ∑_{I ⊆ {1..k}} (-1)^{|I|} [lcm_{i ∈ I} n i ∣ m]`,
and both the finite count and the infinite sum are evaluated term by term, the infinite
sum using the Euler product for `P`-factored numbers.
-/

namespace SunL34_A

open Finset

/-- `n ↦ (n : ℝ)⁻¹` as a monoid homomorphism. -/
private noncomputable def rcp : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' a b := by push_cast; rw [mul_inv]

@[simp] private lemma rcp_apply (n : ℕ) : rcp n = (n : ℝ)⁻¹ := rfl

/-! ### The Euler product over `P`-factored numbers -/

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

/-- The same sum restricted to the multiples of a fixed `P`-factored `a`. -/
private lemma hasSum_factored_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {a : ℕ} (ha : a ∈ Nat.factoredNumbers P) :
    HasSum ((Nat.factoredNumbers P ∩ {m : ℕ | a ∣ m}).indicator fun n : ℕ => ((n : ℝ))⁻¹)
      ((∏ p ∈ P, (p : ℝ) / ((p : ℝ) - 1)) * (a : ℝ)⁻¹) := by
  have ha0 : a ≠ 0 := ha.1
  have hapos : 0 < a := Nat.pos_of_ne_zero ha0
  have hinj : Function.Injective (fun t : ℕ => a * t) :=
    fun x y hxy => Nat.eq_of_mul_eq_mul_left hapos hxy
  have hzero : ∀ x ∉ Set.range (fun t : ℕ => a * t),
      (Nat.factoredNumbers P ∩ {m : ℕ | a ∣ m}).indicator (fun n : ℕ => ((n : ℝ))⁻¹) x = 0 := by
    intro x hx
    refine Set.indicator_of_notMem ?_ _
    rintro ⟨-, hdvd⟩
    obtain ⟨q, rfl⟩ := hdvd
    exact hx ⟨q, rfl⟩
  rw [← hinj.hasSum_iff hzero]
  have hfun : ((Nat.factoredNumbers P ∩ {m : ℕ | a ∣ m}).indicator (fun n : ℕ => ((n : ℝ))⁻¹))
        ∘ (fun t : ℕ => a * t)
      = fun t : ℕ => (a : ℝ)⁻¹ * (Nat.factoredNumbers P).indicator (fun n : ℕ => ((n : ℝ))⁻¹) t := by
    funext t
    simp only [Function.comp_apply]
    by_cases ht : t ∈ Nat.factoredNumbers P
    · rw [Set.indicator_of_mem (Set.mem_inter (Nat.mul_mem_factoredNumbers ha ht)
        (Dvd.intro t rfl)), Set.indicator_of_mem ht]
      push_cast
      rw [mul_inv]
    · rw [Set.indicator_of_notMem ht, mul_zero, Set.indicator_of_notMem]
      rintro ⟨hmem, -⟩
      exact ht (Nat.mem_factoredNumbers_of_dvd hmem (Dvd.intro_left a rfl))
  rw [hfun]
  simpa [mul_comm] using (hasSum_factored P hP).mul_left ((a : ℝ)⁻¹)

/-! ### Inclusion–exclusion -/

private lemma ie_pointwise {k : ℕ} (n : Fin k → ℕ) (m : ℕ) :
    (if ∃ i, n i ∣ m then (1 : ℝ) else 0)
      = 1 - ∑ I ∈ (Finset.univ : Finset (Fin k)).powerset,
              (-1) ^ I.card * (if I.lcm n ∣ m then (1 : ℝ) else 0) := by
  classical
  have h1 : ∀ I : Finset (Fin k), ∏ i ∈ I, (if n i ∣ m then (1 : ℝ) else 0)
      = if I.lcm n ∣ m then (1 : ℝ) else 0 := by
    intro I
    by_cases h : I.lcm n ∣ m
    · rw [if_pos h]
      refine Finset.prod_eq_one fun i hi => ?_
      rw [if_pos ((Finset.dvd_lcm hi).trans h)]
    · rw [if_neg h]
      have : ∃ i ∈ I, ¬ n i ∣ m := by
        by_contra hc
        push_neg at hc
        exact h (Finset.lcm_dvd hc)
      obtain ⟨i, hi, hni⟩ := this
      exact Finset.prod_eq_zero hi (if_neg hni)
  have h2 : ∏ i ∈ (Finset.univ : Finset (Fin k)), (1 - (if n i ∣ m then (1 : ℝ) else 0))
      = if ∃ i, n i ∣ m then (0 : ℝ) else 1 := by
    by_cases h : ∃ i, n i ∣ m
    · obtain ⟨i, hi⟩ := h
      rw [if_pos ⟨i, hi⟩]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [if_pos hi]; ring
    · rw [if_neg h]
      push_neg at h
      refine Finset.prod_eq_one fun i _ => ?_
      rw [if_neg (h i)]; ring
  have h3 := Finset.prod_add (fun i : Fin k => -(if n i ∣ m then (1 : ℝ) else 0))
      (fun _ : Fin k => (1 : ℝ)) Finset.univ
  simp only [neg_add_eq_sub, Finset.prod_const_one, mul_one, Finset.prod_neg] at h3
  rw [h2] at h3
  simp only [h1] at h3
  by_cases h : ∃ i, n i ∣ m
  · rw [if_pos h]
    rw [if_pos h] at h3
    linarith [h3]
  · rw [if_neg h]
    rw [if_neg h] at h3
    linarith [h3]

/-! ### The lcm's are `P`-factored divisors of `N` -/

private lemma primeFactors_prod_subset {k : ℕ} (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (P : Finset ℕ) (hsub : ∀ i, (n i).primeFactors ⊆ P) (I : Finset (Fin k)) :
    (∏ i ∈ I, n i).primeFactors ⊆ P := by
  classical
  induction I using Finset.induction with
  | empty => simp
  | insert i I hi ih =>
      have h1 : n i ≠ 0 := (hn i).ne'
      have h2 : (∏ j ∈ I, n j) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j _ => (hn j).ne'
      rw [Finset.prod_insert hi, Nat.primeFactors_mul h1 h2]
      exact Finset.union_subset (hsub i) ih

private lemma lcm_mem_factored {k : ℕ} (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (P : Finset ℕ) (hsub : ∀ i, (n i).primeFactors ⊆ P) (I : Finset (Fin k)) :
    I.lcm n ∈ Nat.factoredNumbers P := by
  have hprod0 : (∏ i ∈ I, n i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hn j).ne'
  have hdvd : I.lcm n ∣ ∏ i ∈ I, n i :=
    Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem n hi
  have hL0 : I.lcm n ≠ 0 := by
    intro h
    exact hprod0 (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  exact Nat.mem_factoredNumbers_of_primeFactors_subset hL0
    ((Nat.primeFactors_mono hdvd hprod0).trans (primeFactors_prod_subset n hn P hsub I))

/-! ### The density as an alternating sum -/

private lemma density_eq {k : ℕ} (n : Fin k → ℕ) (N : ℕ) (hN : 0 < N) (hdvd : ∀ i, n i ∣ N) :
    ((((Finset.range N).filter fun x => ∃ i, n i ∣ x).card : ℝ) / (N : ℝ))
      = 1 - ∑ I ∈ (Finset.univ : Finset (Fin k)).powerset,
              (-1) ^ I.card * ((I.lcm n : ℕ) : ℝ)⁻¹ := by
  classical
  have hLdvd : ∀ I : Finset (Fin k), I.lcm n ∣ N := fun I =>
    Finset.lcm_dvd fun i _ => hdvd i
  have hL0 : ∀ I : Finset (Fin k), I.lcm n ≠ 0 := by
    intro I h
    exact hN.ne' (Nat.eq_zero_of_zero_dvd (h ▸ hLdvd I))
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcard : ((((Finset.range N).filter fun x => ∃ i, n i ∣ x).card : ℝ))
      = (N : ℝ) * (1 - ∑ I ∈ (Finset.univ : Finset (Fin k)).powerset,
              (-1) ^ I.card * ((I.lcm n : ℕ) : ℝ)⁻¹) := by
    rw [← Finset.sum_boole]
    calc ∑ x ∈ Finset.range N, (if ∃ i, n i ∣ x then (1 : ℝ) else 0)
        = ∑ x ∈ Finset.range N, (1 - ∑ I ∈ (Finset.univ : Finset (Fin k)).powerset,
              (-1) ^ I.card * (if I.lcm n ∣ x then (1 : ℝ) else 0)) := by
          exact Finset.sum_congr rfl fun x _ => ie_pointwise n x
      _ = (N : ℝ) - ∑ I ∈ (Finset.univ : Finset (Fin k)).powerset,
              (-1) ^ I.card * ∑ x ∈ Finset.range N, (if I.lcm n ∣ x then (1 : ℝ) else 0) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_one, Finset.sum_comm]
          congr 1
          exact Finset.sum_congr rfl fun I _ => by rw [Finset.mul_sum]
      _ = (N : ℝ) * (1 - ∑ I ∈ (Finset.univ : Finset (Fin k)).powerset,
              (-1) ^ I.card * ((I.lcm n : ℕ) : ℝ)⁻¹) := by
          have hterm : ∀ I : Finset (Fin k),
              ∑ x ∈ Finset.range N, (if I.lcm n ∣ x then (1 : ℝ) else 0)
                = (N : ℝ) * ((I.lcm n : ℕ) : ℝ)⁻¹ := by
            intro I
            rw [Finset.sum_boole, SunDev.card_filter_dvd_range (hLdvd I) (hL0 I),
              Nat.cast_div (hLdvd I) (Nat.cast_ne_zero.mpr (hL0 I)), div_eq_mul_inv]
          rw [Finset.sum_congr rfl fun I _ => by rw [hterm I]]
          rw [mul_sub, mul_one, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun I _ => by ring
  rw [hcard, mul_comm, mul_div_assoc, div_self hN0, mul_one]

/-! ### Main theorem -/

theorem hasSum_smooth_reciprocals {k : ℕ} (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (N : ℕ) (hN : 0 < N) (hdvd : ∀ i, n i ∣ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hsub : ∀ i, (n i).primeFactors ⊆ P) :
    HasSum (fun m : {m : ℕ // 0 < m ∧ m.primeFactors ⊆ P ∧ ∃ i, n i ∣ m} =>
        (1 : ℝ) / ((m : ℕ) : ℝ))
      ((((Finset.range N).filter fun x => ∃ i, n i ∣ x).card : ℝ) / (N : ℝ)
        * ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1))) := by
  classical
  set C : ℝ := ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1)) with hC
  set S : Set ℕ := {m : ℕ | 0 < m ∧ m.primeFactors ⊆ P ∧ ∃ i, n i ∣ m} with hS
  set T : Set ℕ := Nat.factoredNumbers P with hT
  set f : ℕ → ℝ := fun n : ℕ => ((n : ℝ))⁻¹ with hf
  have hmemT : ∀ m : ℕ, m ∈ T ↔ (m ≠ 0 ∧ m.primeFactors ⊆ P) := fun m =>
    Nat.mem_factoredNumbers_iff_primeFactors_subset
  -- the pieces
  have hbase : HasSum (T.indicator f) C := hasSum_factored P hP
  have hpiece : ∀ I ∈ (Finset.univ : Finset (Fin k)).powerset,
      HasSum (fun m : ℕ => (-1 : ℝ) ^ I.card * (T ∩ {m : ℕ | I.lcm n ∣ m}).indicator f m)
        ((-1 : ℝ) ^ I.card * (C * ((I.lcm n : ℕ) : ℝ)⁻¹)) := by
    intro I _
    exact (hasSum_factored_dvd P hP (lcm_mem_factored n hn P hsub I)).mul_left _
  have hsum := hbase.sub (hasSum_sum hpiece)
  -- identify the function
  have hfunext : (fun m : ℕ => T.indicator f m
        - ∑ I ∈ (Finset.univ : Finset (Fin k)).powerset,
            (-1 : ℝ) ^ I.card * (T ∩ {m : ℕ | I.lcm n ∣ m}).indicator f m)
      = S.indicator f := by
    funext m
    by_cases hm : m ∈ T
    · have hmS : (m ∈ S) ↔ (∃ i, n i ∣ m) := by
        rw [hmemT] at hm
        simp only [hS, Set.mem_setOf_eq]
        exact ⟨fun h => h.2.2, fun h => ⟨Nat.pos_of_ne_zero hm.1, hm.2, h⟩⟩
      have hind : ∀ I : Finset (Fin k),
          (T ∩ {m : ℕ | I.lcm n ∣ m}).indicator f m
            = f m * (if I.lcm n ∣ m then (1 : ℝ) else 0) := by
        intro I
        by_cases hI : I.lcm n ∣ m
        · rw [Set.indicator_of_mem (Set.mem_inter hm hI) f, if_pos hI, mul_one]
        · rw [Set.indicator_of_notMem (by rintro ⟨-, h⟩; exact hI h), if_neg hI, mul_zero]
      have hSind : S.indicator f m = f m * (if ∃ i, n i ∣ m then (1 : ℝ) else 0) := by
        by_cases hx : ∃ i, n i ∣ m
        · rw [Set.indicator_of_mem (hmS.mpr hx), if_pos hx, mul_one]
        · rw [Set.indicator_of_notMem (fun h => hx (hmS.mp h)), if_neg hx, mul_zero]
      rw [Set.indicator_of_mem hm, hSind, ie_pointwise n m]
      simp only [hind]
      rw [mul_sub, mul_one, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun I _ => by ring
    · have hmS : m ∉ S := by
        intro h
        exact hm ((hmemT m).mpr ⟨h.1.ne', h.2.1⟩)
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hmS]
      have : ∀ I : Finset (Fin k), (T ∩ {m : ℕ | I.lcm n ∣ m}).indicator f m = 0 := by
        intro I
        exact Set.indicator_of_notMem (fun h => hm h.1) _
      simp only [this, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [hfunext] at hsum
  -- identify the value
  have hval : C - ∑ I ∈ (Finset.univ : Finset (Fin k)).powerset,
        (-1 : ℝ) ^ I.card * (C * ((I.lcm n : ℕ) : ℝ)⁻¹)
      = ((((Finset.range N).filter fun x => ∃ i, n i ∣ x).card : ℝ) / (N : ℝ)) * C := by
    rw [density_eq n N hN hdvd, sub_mul, one_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun I _ => by ring
  rw [hval] at hsum
  rw [← hasSum_subtype_iff_indicator] at hsum
  simp only [hf, Function.comp_def] at hsum
  simp only [one_div]
  exact hsum

end SunL34_A

theorem solution {k : ℕ} (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (N : ℕ) (hN : 0 < N) (hdvd : ∀ i, n i ∣ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hsub : ∀ i, (n i).primeFactors ⊆ P) :
    HasSum (fun m : {m : ℕ // 0 < m ∧ m.primeFactors ⊆ P ∧ ∃ i, n i ∣ m} =>
        (1 : ℝ) / ((m : ℕ) : ℝ))
      ((((Finset.range N).filter fun x => ∃ i, n i ∣ x).card : ℝ) / (N : ℝ)
        * ∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1))) :=
  SunL34_A.hasSum_smooth_reciprocals n hn N hN hdvd P hP hsub
