-- Prove2me | solution 1 for PCSPBLPAff.Characterization.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T10:23:47.383193+00:00
-- url     : https://prove2.me/submissions/eddad387-f769-4a0f-a409-d889b1c093a8

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting
import Theorems.Thm_PCSPBLPAff_Characterization_lemma_16

open PCSPBLPAff.Symmetric PCSPBLPAff.Characterization

namespace PCSPBLPAff.Characterization.L9aux

theorem exists_perm_of_fiber_card {T K : Type} [Fintype T] [DecidableEq K] (g₁ g₂ : T → K)
    (h : ∀ k, (Finset.univ.filter (fun t => g₁ t = k)).card =
      (Finset.univ.filter (fun t => g₂ t = k)).card) :
    ∃ σ : Equiv.Perm T, ∀ t, g₂ (σ t) = g₁ t := by
  classical
  refine ⟨Equiv.ofFiberEquiv (f := g₁) (g := g₂) (fun k => Fintype.equivOfCardEq ?_),
    fun t => Equiv.ofFiberEquiv_map _ t⟩
  rw [Fintype.card_subtype, Fintype.card_subtype, h k]

theorem polMinor_eq_of_counts {A B : Type} {L Lf κ : ℕ} (β : Fin Lf → Fin κ)
    (f : (Fin Lf → A) → B) (hf : IsBlockSymmetricFor β f) (π₁ π₂ : Fin Lf → Fin L)
    (h : ∀ b i, (Finset.univ.filter (fun l => (β l, π₁ l) = (b, i))).card =
      (Finset.univ.filter (fun l => (β l, π₂ l) = (b, i))).card) :
    polMinor π₁ f = polMinor π₂ f := by
  obtain ⟨σ, hσ⟩ := exists_perm_of_fiber_card (fun l => (β l, π₁ l)) (fun l => (β l, π₂ l))
    (fun k => h k.1 k.2)
  funext x
  have h1 : ∀ l, β (σ l) = β l := fun l => congrArg Prod.fst (hσ l)
  have h2 : ∀ l, π₂ (σ l) = π₁ l := fun l => congrArg Prod.snd (hσ l)
  simp only [polMinor]
  rw [← hf σ h1 (x ∘ π₂)]
  congr 1
  funext l
  simp [h2]

theorem exists_map_of_counts {T I : Type} [Fintype T] [Fintype I] [DecidableEq I] (c : I → ℕ)
    (hc : ∑ i, c i = Fintype.card T) :
    ∃ g : T → I, ∀ i, (Finset.univ.filter (fun t => g t = i)).card = c i := by
  classical
  let e : T ≃ Σ i, Fin (c i) := Fintype.equivOfCardEq (by simp [Fintype.card_sigma, hc])
  refine ⟨fun t => (e t).1, fun i => ?_⟩
  rw [Finset.card_filter]
  rw [Fintype.sum_equiv e (fun t => if (e t).1 = i then 1 else 0)
    (fun y => if y.1 = i then 1 else 0) (fun _ => rfl)]
  rw [Fintype.sum_sigma]
  simp [apply_ite Finset.card]

theorem exists_map_of_block_counts {T K I : Type} [Fintype T] [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I] (β : T → K) (c : K → I → ℕ)
    (hc : ∀ k, ∑ i, c k i = (Finset.univ.filter (fun t => β t = k)).card) :
    ∃ π : T → I, ∀ k i, (Finset.univ.filter (fun t => (β t, π t) = (k, i))).card = c k i := by
  classical
  have htot : ∑ p : K × I, c p.1 p.2 = Fintype.card T := by
    rw [Fintype.sum_prod_type]
    simp_rw [hc]
    rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _), Finset.card_univ]
  obtain ⟨g, hg⟩ := exists_map_of_counts (fun p : K × I => c p.1 p.2) htot
  have hfst : ∀ k, (Finset.univ.filter (fun t => β t = k)).card =
      (Finset.univ.filter (fun t => (g t).1 = k)).card := by
    intro k
    rw [← hc k]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun t => (g t).2) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (hg (k, i)).symm.trans ?_
    rw [Finset.filter_filter]
    congr 1
    ext t
    simp [Prod.ext_iff]
  obtain ⟨σ, hσ⟩ := exists_perm_of_fiber_card β (fun t => (g t).1) hfst
  refine ⟨fun t => (g (σ t)).2, fun k i => ?_⟩
  have hpair : ∀ t, (β t, (g (σ t)).2) = g (σ t) := fun t => Prod.ext (hσ t).symm rfl
  simp_rw [hpair]
  refine Eq.trans ?_ (hg (k, i))
  rw [Finset.card_filter, Finset.card_filter]
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

theorem isPolymorphism_polMinor {τ : Type} {ar : τ → ℕ} {A B : Type} {𝔸 : RelStruct τ ar A}
    {𝔹 : RelStruct τ ar B} {L L' : ℕ} (π : Fin L → Fin L') {f : (Fin L → A) → B}
    (hf : IsPolymorphism 𝔸 𝔹 f) : IsPolymorphism 𝔸 𝔹 (polMinor π f) :=
  fun R M hM => hf R (fun l => M (π l)) (fun l => hM (π l))

/-- block counts of `π` (as rationals). -/
def bc {Lf κ L : ℕ} (β : Fin Lf → Fin κ) (π : Fin Lf → Fin L) (b : Fin κ) (i : Fin L) : ℚ :=
  ((Finset.univ.filter (fun l => (β l, π l) = (b, i))).card : ℚ)

/-- size of block `b`. -/
def nb {Lf κ : ℕ} (β : Fin Lf → Fin κ) (b : Fin κ) : ℕ :=
  (Finset.univ.filter (fun l => β l = b)).card

/-- `π` realises the object `x` in every block: in block `b` (of size `uℓ + v`, `v < ℓ`),
coordinate `i` is hit `uℓ w(i) + v r(i)` times. -/
def Good {Lf κ L : ℕ} (β : Fin Lf → Fin κ) (ℓ : ℕ) (x : BLPAffObj (Fin L))
    (π : Fin Lf → Fin L) : Prop :=
  ∀ b i, bc β π b i = ((nb β b / ℓ : ℕ) : ℚ) * ℓ * x.1.1 i + ((nb β b % ℓ : ℕ) : ℚ) * (x.1.2 i : ℚ)

theorem bc_comp {Lf κ L L' : ℕ} (β : Fin Lf → Fin κ) (π : Fin Lf → Fin L) (ρ : Fin L → Fin L')
    (b : Fin κ) (i' : Fin L') :
    bc β (ρ ∘ π) b i' = ∑ i ∈ Finset.univ.filter (fun i => ρ i = i'), bc β π b i := by
  unfold bc
  rw [← Nat.cast_sum]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ.filter (fun i => ρ i = i')) ?_]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [Finset.filter_filter]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq, Function.comp_apply]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hi.2⟩, h3⟩
  · intro l hl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, Prod.mk.injEq,
      Function.comp_apply] at hl ⊢
    exact hl.2

theorem good_minor {Lf κ L L' : ℕ} (β : Fin Lf → Fin κ) (ℓ : ℕ) (x : BLPAffObj (Fin L))
    (π : Fin Lf → Fin L) (hg : Good β ℓ x π) (ρ : Fin L → Fin L')
    (h : IsBLPAffObj (minorQ ρ x.1.1) (minorZ ρ x.1.2)) :
    Good β ℓ ⟨(minorQ ρ x.1.1, minorZ ρ x.1.2), h⟩ (ρ ∘ π) := by
  intro b i'
  rw [bc_comp, Finset.sum_congr rfl (fun i _ => hg b i)]
  simp only [minorQ, minorZ, Int.cast_sum, Finset.mul_sum, Finset.sum_add_distrib]

theorem obj_pos {L : ℕ} (x : BLPAffObj (Fin L)) : 0 < L := by
  rcases Nat.eq_zero_or_pos L with rfl | h
  · have := x.2.2.1; simp at this
  · exact h

theorem exists_good {Lf κ L : ℕ} (β : Fin Lf → Fin κ) (ℓ M : ℕ) (hℓ : 0 < ℓ)
    (hβ : ∀ b, M * ℓ ^ 2 ≤ nb β b) (x : BLPAffObj (Fin L))
    (hz : ∀ i, ∃ z : ℤ, (ℓ : ℚ) * x.1.1 i = z) (hM : ∑ i, |x.1.2 i| ≤ (M : ℤ)) :
    ∃ π, Good β ℓ x π := by
  choose z hz using hz
  obtain ⟨h0, h1, h2, h3⟩ := x.2
  let W : Fin κ → Fin L → ℤ := fun b i => ((nb β b / ℓ : ℕ) : ℤ) * z i + ((nb β b % ℓ : ℕ) : ℤ) * x.1.2 i
  have hW0 : ∀ b i, 0 ≤ W b i := by
    intro b i
    by_cases hw : x.1.1 i = 0
    · have hr : x.1.2 i = 0 := h3 i hw
      have hzi : z i = 0 := by
        have := hz i; rw [hw, mul_zero] at this; exact_mod_cast this.symm
      simp [W, hr, hzi]
    · have hwpos : 0 < x.1.1 i := lt_of_le_of_ne (h0 i) (Ne.symm hw)
      have hz1 : 1 ≤ z i := by
        have : (0 : ℚ) < z i := by rw [← hz i]; positivity
        exact_mod_cast this
      have hu : M * ℓ ≤ nb β b / ℓ := by
        rw [Nat.le_div_iff_mul_le hℓ]; nlinarith [hβ b]
      have hv : nb β b % ℓ < ℓ := Nat.mod_lt _ hℓ
      have hri : |x.1.2 i| ≤ (M : ℤ) :=
        le_trans (Finset.single_le_sum (fun j _ => abs_nonneg (x.1.2 j)) (Finset.mem_univ i)) hM
      have hneg : -(M : ℤ) ≤ x.1.2 i := le_trans (neg_le_neg hri) (neg_abs_le _)
      set u : ℤ := ((nb β b / ℓ : ℕ) : ℤ) with hu_def
      set v : ℤ := ((nb β b % ℓ : ℕ) : ℤ) with hv_def
      have hu' : (M : ℤ) * ℓ ≤ u := by rw [hu_def]; exact_mod_cast hu
      have hv' : v ≤ ℓ := by rw [hv_def]; exact_mod_cast hv.le
      have hv0 : 0 ≤ v := by rw [hv_def]; positivity
      have hM0 : (0 : ℤ) ≤ M := by positivity
      have e1 : u * 1 ≤ u * z i := mul_le_mul_of_nonneg_left hz1 (by nlinarith)
      have e2 : v * (-(M : ℤ)) ≤ v * x.1.2 i := mul_le_mul_of_nonneg_left hneg hv0
      have e3 : v * (M : ℤ) ≤ ℓ * M := mul_le_mul_of_nonneg_right hv' hM0
      show 0 ≤ u * z i + v * x.1.2 i
      nlinarith
  have hzsum : ∑ i, z i = ℓ := by
    have : ((∑ i, z i : ℤ) : ℚ) = ℓ := by
      push_cast
      simp_rw [← hz]
      rw [← Finset.mul_sum, h1, mul_one]
    exact_mod_cast this
  have hWsum : ∀ b, ∑ i, W b i = nb β b := by
    intro b
    simp only [W, Finset.sum_add_distrib, ← Finset.mul_sum, hzsum, h2, mul_one]
    have hdm : (nb β b / ℓ) * ℓ + nb β b % ℓ = nb β b := by
      rw [mul_comm]; exact Nat.div_add_mod _ _
    have : ((nb β b / ℓ : ℕ) : ℤ) * ℓ + ((nb β b % ℓ : ℕ) : ℤ) = nb β b := by
      exact_mod_cast hdm
    linarith
  obtain ⟨π, hπ⟩ := exists_map_of_block_counts β (fun b i => (W b i).toNat) (fun b => by
    have : ((∑ i, (W b i).toNat : ℕ) : ℤ) = nb β b := by
      push_cast
      rw [← hWsum b]
      exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hW0 b i)
    exact_mod_cast this)
  refine ⟨π, fun b i => ?_⟩
  unfold bc
  rw [hπ b i]
  have e : (((W b i).toNat : ℕ) : ℚ) = ((W b i : ℤ) : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hW0 b i)]
  rw [e]
  simp only [W, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [← hz i]
  ring

end PCSPBLPAff.Characterization.L9aux

namespace PCSPBLPAff.Characterization.L9aux

/-- arities of the auxiliary signature `Option τ` (`none` = binary equality symbol). -/
def ar' {τ : Type} (ar : τ → ℕ) : Option τ → ℕ
  | none => 2
  | some R => ar R

/-- pairs (object, input tuple). -/
abbrev Dom (A : Type) : Type := Σ L : ℕ, BLPAffObj (Fin L) × (Fin L → A)

def e0 {τ : Type} (ar : τ → ℕ) : Fin (ar' ar none) := ⟨0, by show 0 < 2; norm_num⟩
def e1 {τ : Type} (ar : τ → ℕ) : Fin (ar' ar none) := ⟨1, by show 1 < 2; norm_num⟩

/-- the structure encoding minor identities (symbol `none`) and polymorphism conditions. -/
def FS {τ : Type} {ar : τ → ℕ} {A : Type} (𝔸 : RelStruct τ ar A) :
    RelStruct (Option τ) (ar' ar) (Dom A) where
  rel
    | none => {t | ∃ (L L' : ℕ) (π : Fin L → Fin L') (x : BLPAffObj (Fin L))
        (h : IsBLPAffObj (minorQ π x.1.1) (minorZ π x.1.2)) (a : Fin L' → A),
        t (e0 ar) = ⟨L', ⟨(minorQ π x.1.1, minorZ π x.1.2), h⟩, a⟩ ∧ t (e1 ar) = ⟨L, x, a ∘ π⟩}
    | some R => {t | ∃ (L : ℕ) (x : BLPAffObj (Fin L)) (M : Fin L → Fin (ar R) → A),
        (∀ l, M l ∈ 𝔸.rel R) ∧ ∀ c, t c = ⟨L, x, fun l => M l c⟩}

def BS {τ : Type} {ar : τ → ℕ} {B : Type} (𝔹 : RelStruct τ ar B) :
    RelStruct (Option τ) (ar' ar) B where
  rel
    | none => {t | t (e0 ar) = t (e1 ar)}
    | some R => 𝔹.rel R

theorem finite_part {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (h : ∀ N : ℕ, ∃ (L : ℕ) (f : (Fin L → A) → B), IsPolymorphism 𝔸 𝔹 f ∧ HasWidthAtLeast f N)
    (S : Finset (Dom A)) :
    ∃ σ : Dom A → B, ∀ R : Option τ, ∀ t ∈ (FS 𝔸).rel R, (∀ k, t k ∈ S) →
      σ ∘ t ∈ (BS 𝔹).rel R := by
  classical
  let ℓ : ℕ := ∏ s ∈ S, ∏ i, ((s.2.1).1.1 i).den
  have hℓ : 0 < ℓ := Finset.prod_pos fun s _ => Finset.prod_pos fun i _ => Rat.den_pos _
  let Mb : ℕ := ∑ s ∈ S, (∑ i, |(s.2.1).1.2 i|).toNat
  obtain ⟨Lf, f, hf, κ, β, -, hβ, hbs⟩ := h (Mb * ℓ ^ 2)
  let πx : (L : ℕ) → BLPAffObj (Fin L) → Fin Lf → Fin L := fun L x =>
    if hx : ∃ π, Good β ℓ x π then hx.choose else fun _ => ⟨0, obj_pos x⟩
  have hπx : ∀ (L : ℕ) (x : BLPAffObj (Fin L)), (∃ π, Good β ℓ x π) → Good β ℓ x (πx L x) := by
    intro L x hx; simp only [πx, dif_pos hx]; exact hx.choose_spec
  refine ⟨fun s => f (s.2.2 ∘ πx s.1 s.2.1), ?_⟩
  rintro (_ | R) t ht hS
  · obtain ⟨L, L', π, x, hm, a, h0, h1⟩ := ht
    have hxS : (⟨L, x, a ∘ π⟩ : Dom A) ∈ S := by rw [← h1]; exact hS _
    have hz : ∀ i, ∃ z : ℤ, (ℓ : ℚ) * x.1.1 i = z := by
      intro i
      have hd : (x.1.1 i).den ∣ ℓ :=
        dvd_trans (Finset.dvd_prod_of_mem (fun i => (x.1.1 i).den) (Finset.mem_univ i))
          (Finset.dvd_prod_of_mem (fun s : Dom A => ∏ i, ((s.2.1).1.1 i).den) hxS)
      obtain ⟨k, hk⟩ := hd
      refine ⟨k * (x.1.1 i).num, ?_⟩
      rw [hk]; push_cast
      rw [← Rat.mul_den_eq_num]; ring
    have hM : ∑ i, |x.1.2 i| ≤ (Mb : ℤ) := by
      have h1' := Finset.single_le_sum (f := fun s : Dom A => (∑ i, |(s.2.1).1.2 i|).toNat)
        (fun _ _ => Nat.zero_le _) hxS
      have h2' : ∑ i, |x.1.2 i| = ((∑ i, |x.1.2 i|).toNat : ℤ) :=
        (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).symm
      rw [h2']; exact_mod_cast h1'
    have gx := hπx L x (exists_good β ℓ Mb hℓ hβ x hz hM)
    have gm := good_minor β ℓ x (πx L x) gx π hm
    have gm' := hπx L' _ ⟨_, gm⟩
    have heq := polMinor_eq_of_counts β f hbs (πx L' ⟨(minorQ π x.1.1, minorZ π x.1.2), hm⟩)
      (π ∘ πx L x) (fun b i => by
        have := (gm' b i).trans (gm b i).symm
        unfold bc at this; exact_mod_cast this)
    show f ((t (e0 ar)).2.2 ∘ πx (t (e0 ar)).1 (t (e0 ar)).2.1) =
      f ((t (e1 ar)).2.2 ∘ πx (t (e1 ar)).1 (t (e1 ar)).2.1)
    rw [h0, h1]
    exact congrFun heq a
  · obtain ⟨L, x, M, hM, htc⟩ := ht
    have : (fun s : Dom A => f (s.2.2 ∘ πx s.1 s.2.1)) ∘ t =
        fun c => f (fun l => M (πx L x l) c) := by
      funext c; rw [Function.comp_apply, htc c]; rfl
    rw [this]
    exact hf R (fun l => M (πx L x l)) (fun l => hM _)

end PCSPBLPAff.Characterization.L9aux

open PCSPBLPAff.Characterization.L9aux in
theorem PCSPBLPAff.Characterization.lemma_9_main {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A]
    [DecidableEq A] [Fintype B] (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (h : ∀ N : ℕ, ∃ (L : ℕ) (f : (Fin L → A) → B), IsPolymorphism 𝔸 𝔹 f ∧ HasWidthAtLeast f N) :
    HasMinionHomToPol 𝔸 𝔹 := by
  classical
  obtain ⟨σ, hσ⟩ := lemma_16 (FS 𝔸) (BS 𝔹) (fun S => finite_part 𝔸 𝔹 h S)
  refine ⟨fun L x a => σ ⟨L, x, a⟩, fun L x => ⟨?_, ?_⟩⟩
  · intro R M hM
    exact hσ (some R) (fun c => ⟨L, x, fun l => M l c⟩) ⟨L, x, M, hM, fun c => rfl⟩
  · intro L' π hm
    funext a
    exact hσ none (show Fin (ar' ar none) → Dom A from
      ![⟨L', ⟨(minorQ π x.1.1, minorZ π x.1.2), hm⟩, a⟩, ⟨L, x, a ∘ π⟩])
      ⟨L, L', π, x, hm, a, rfl, rfl⟩

open PCSPBLPAff.Characterization in
/-- Lemma 9, p. 11. -/
theorem solution {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B)
    (h : ∀ N : ℕ, ∃ (L : ℕ) (f : (Fin L → A) → B),
      PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 f ∧ PCSPBLPAff.Symmetric.HasWidthAtLeast f N) :
    HasMinionHomToPol 𝔸 𝔹 :=
  PCSPBLPAff.Characterization.lemma_9_main 𝔸 𝔹 h
