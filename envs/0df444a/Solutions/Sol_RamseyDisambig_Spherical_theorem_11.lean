-- Prove2me | solution 1 for RamseyDisambig.Spherical.theorem_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:21:19.393645+00:00
-- url     : https://prove2.me/submissions/c2eafe11-e53f-414c-a739-31f9a1f3d102
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RamseyDisambig_Spherical_BlockMaps
import Theorems.Thm_Palvolgyi2026_kneser_shift

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {X : Type v}
/-! Blueprint: Pálvölgyi's Dense Block theorem (RamseyDisambig.Spherical.theorem_11) from the
Kneser-shift theorem (Palvolgyi2026.kneser_shift), following Sections 3, 5, 6 of arXiv:2608.10865. -/
/-! ## Part A: the framework -/
/-- Single-coordinate insensitivity of `g` to the relation `S`. -/
def Ins {ι : Type*} [DecidableEq ι] {β : Type*} (S : X → X → Prop) (g : (ι → X) → β) : Prop :=
  ∀ (x : ι → X) (i : ι) (a : X), S (x i) a → g x = g (Function.update x i a)

/-- A block map whose labels satisfy `L`: coordinate `ℓ` copies variable `blk ℓ` through `f ℓ`,
or is the constant `z ℓ` when `blk ℓ = none`; every variable occupies exactly `k` coordinates. -/
def IsBlk (L : (X → X) → Prop) (m n k : ℕ) (φ : (Fin m → X) → (Fin n → X)) : Prop :=
  ∃ (blk : Fin n → Option (Fin m)) (f : Fin n → X → X) (z : Fin n → X),
    (∀ ℓ, L (f ℓ)) ∧
    (∀ j, (Finset.univ.filter (fun ℓ => blk ℓ = some j)).card = k) ∧
    ∀ x ℓ, φ x ℓ = (blk ℓ).elim (z ℓ) (fun j => f ℓ (x j))

/-- Relative dense block step: every `E`-insensitive coloring admits a dense block map making it
`E'`-insensitive. -/
def Step (L : (X → X) → Prop) (E E' : X → X → Prop) : Prop :=
  ∀ r m : ℕ, 1 ≤ m → ∀ η : ℝ, 0 < η → η < 1 →
    ∃ n k : ℕ, 1 ≤ n ∧ 1 ≤ k ∧ (1 - η) * (n : ℝ) ≤ (m : ℝ) * (k : ℝ) ∧
      ∀ c : (Fin n → X) → Fin r, Ins E c →
        ∃ φ : (Fin m → X) → (Fin n → X), IsBlk L m n k φ ∧ Ins E' (c ∘ φ)

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartA
open RamseyDisambig.Dev.DB Classical
universe u v
variable {X : Type v}
theorem Ins_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} {S : X → X → Prop}
    {g : (ι → X) → β} (hg : Ins S g) (w w' : ι → X) (h : ∀ ℓ, w ℓ = w' ℓ ∨ S (w ℓ) (w' ℓ)) :
    g w = g w' := by
  have key : ∀ s : Finset ι, g w = g (fun ℓ => if ℓ ∈ s then w' ℓ else w ℓ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [ih]
      have hupd : (fun ℓ => if ℓ ∈ insert a s then w' ℓ else w ℓ) =
          Function.update (fun ℓ => if ℓ ∈ s then w' ℓ else w ℓ) a (w' a) := by
        funext ℓ
        by_cases hℓ : ℓ = a
        · subst hℓ; simp
        · simp [Finset.mem_insert, hℓ]
      rw [hupd]
      rcases h a with h1 | h1
      · rw [Function.update_eq_self_iff.mpr (by simp [ha, h1])]
      · exact hg _ a _ (by simpa [ha] using h1)
  simpa using key Finset.univ

end RamseyDisambig.Dev.DB.PartA
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {X : Type v}
alias Ins_congr := RamseyDisambig.Dev.DB.PartA.Ins_congr

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartA
open RamseyDisambig.Dev.DB Classical
universe u v
variable {X : Type v}
theorem IsBlk_comp {L : (X → X) → Prop} (hL : ∀ f g, L f → L g → L (f ∘ g))
    {m n₀ n k₁ k₂ : ℕ} {Φ : (Fin n₀ → X) → (Fin n → X)} {Ψ : (Fin m → X) → (Fin n₀ → X)}
    (hΦ : IsBlk L n₀ n k₁ Φ) (hΨ : IsBlk L m n₀ k₂ Ψ) : IsBlk L m n (k₁ * k₂) (Φ ∘ Ψ) := by
  obtain ⟨b₁, f₁, z₁, hf₁, hc₁, hΦ⟩ := hΦ
  obtain ⟨b₂, f₂, z₂, hf₂, hc₂, hΨ⟩ := hΨ
  refine ⟨fun ℓ => (b₁ ℓ).bind b₂,
    fun ℓ => (b₁ ℓ).elim (f₁ ℓ) (fun i => f₁ ℓ ∘ f₂ i),
    fun ℓ => (b₁ ℓ).elim (z₁ ℓ) (fun i => f₁ ℓ (z₂ i)), ?_, ?_, ?_⟩
  · intro ℓ
    rcases hb : b₁ ℓ with _ | i
    · simpa [hb] using hf₁ ℓ
    · simpa [hb] using hL _ _ (hf₁ ℓ) (hf₂ i)
  · intro j
    have hs : (Finset.univ.filter (fun ℓ => (b₁ ℓ).bind b₂ = some j)) =
        (Finset.univ.filter (fun i => b₂ i = some j)).biUnion
          (fun i => Finset.univ.filter (fun ℓ => b₁ ℓ = some i)) := by
      ext ℓ; simp [Option.bind_eq_some_iff, and_comm]
    rw [hs, Finset.card_biUnion]
    · simp [hc₁, hc₂, mul_comm]
    · intro i _ i' _ hii'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro ℓ h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hii' (Option.some_injective _ (h1.symm.trans h2))
  · intro x ℓ
    simp only [Function.comp, hΦ, hΨ]
    rcases hb : b₁ ℓ with _ | i
    · simp
    · rcases hb2 : b₂ i with _ | j <;> simp [hb2]

end RamseyDisambig.Dev.DB.PartA
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {X : Type v}
alias IsBlk_comp := RamseyDisambig.Dev.DB.PartA.IsBlk_comp

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartA
open RamseyDisambig.Dev.DB Classical
universe u v
variable {X : Type v}
theorem Ins_comp {L : (X → X) → Prop} {E : X → X → Prop}
    (hE : ∀ f, L f → ∀ a b, E a b → E (f a) (f b)) {m n k : ℕ} {φ : (Fin m → X) → (Fin n → X)}
    (hφ : IsBlk L m n k φ) {β : Type*} {c : (Fin n → X) → β} (hc : Ins E c) : Ins E (c ∘ φ) := by
  obtain ⟨blk, f, z, hf, -, hφ⟩ := hφ
  intro x i a hxa
  refine Ins_congr hc _ _ (fun ℓ => ?_)
  rw [hφ, hφ]
  rcases hb : blk ℓ with _ | j
  · left; rfl
  · by_cases hji : j = i
    · subst hji; right; simpa using hE _ (hf ℓ) _ _ hxa
    · left; simp [Function.update_of_ne hji]

end RamseyDisambig.Dev.DB.PartA
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {X : Type v}
alias Ins_comp := RamseyDisambig.Dev.DB.PartA.Ins_comp

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartA
open RamseyDisambig.Dev.DB Classical
universe u v
variable {X : Type v}
theorem Step_refl [Nonempty X] {L : (X → X) → Prop} (hL : L id) (E : X → X → Prop) : Step L E E := by
  intro r m hm η hη hη1
  refine ⟨m, 1, hm, le_rfl, by push_cast; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)], fun c hc => ?_⟩
  refine ⟨id, ⟨fun ℓ => some ℓ, fun _ => id, fun _ => Classical.arbitrary X,
    fun _ => hL, fun j => ?_, fun x ℓ => rfl⟩, hc⟩
  rw [Finset.card_eq_one]
  exact ⟨j, by ext ℓ; simp⟩

end RamseyDisambig.Dev.DB.PartA
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {X : Type v}
alias Step_refl := RamseyDisambig.Dev.DB.PartA.Step_refl

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartA
open RamseyDisambig.Dev.DB Classical
universe u v
variable {X : Type v}
theorem dens_comb {η : ℝ} (hη : 0 < η) (hη1 : η < 1) {n n₀ m k₁ k₂ : ℕ}
    (h₁ : (1 - η / 2) * (n : ℝ) ≤ (n₀ : ℝ) * (k₁ : ℝ))
    (h₂ : (1 - η / 2) * (n₀ : ℝ) ≤ (m : ℝ) * (k₂ : ℝ)) :
    (1 - η) * (n : ℝ) ≤ (m : ℝ) * ((k₁ * k₂ : ℕ) : ℝ) := by
  push_cast
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk : (0 : ℝ) ≤ k₁ := Nat.cast_nonneg k₁
  have ha : 0 ≤ 1 - η / 2 := by linarith
  have e1 : (1 - η) * (n : ℝ) ≤ (1 - η / 2) * ((1 - η / 2) * n) := by
    nlinarith [mul_nonneg (sq_nonneg η) hn]
  have e2 : (1 - η / 2) * ((1 - η / 2) * n) ≤ (1 - η / 2) * (n₀ * k₁) :=
    mul_le_mul_of_nonneg_left h₁ ha
  have e3 : (1 - η / 2) * (n₀ * k₁) ≤ m * k₂ * k₁ := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h₂ hk
  nlinarith

theorem Step_trans {L : (X → X) → Prop} (hL : ∀ f g, L f → L g → L (f ∘ g))
    {E₁ E₂ E₃ : X → X → Prop} (h₁ : Step L E₁ E₂) (h₂ : Step L E₂ E₃) : Step L E₁ E₃ := by
  intro r m hm η hη hη1
  obtain ⟨n₀, k₂, hn₀, hk₂, hd₂, H₂⟩ := h₂ r m hm (η / 2) (by linarith) (by linarith)
  obtain ⟨n, k₁, hn, hk₁, hd₁, H₁⟩ := h₁ r n₀ hn₀ (η / 2) (by linarith) (by linarith)
  refine ⟨n, k₁ * k₂, hn, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    dens_comb hη hη1 hd₁ hd₂, fun c hc => ?_⟩
  obtain ⟨Φ, hΦ, hcΦ⟩ := H₁ c hc
  obtain ⟨Ψ, hΨ, hcΨ⟩ := H₂ (c ∘ Φ) hcΦ
  exact ⟨Φ ∘ Ψ, IsBlk_comp hL hΦ hΨ, hcΨ⟩

end RamseyDisambig.Dev.DB.PartA
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {X : Type v}
alias Step_trans := RamseyDisambig.Dev.DB.PartA.Step_trans

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartA
open RamseyDisambig.Dev.DB Classical
universe u v
variable {X : Type v}
theorem Step_mono {L L' : (X → X) → Prop} {E₁ E₂ E₁' E₂' : X → X → Prop}
    (h : Step L E₁ E₂) (hL : ∀ f, L f → L' f) (h₁ : ∀ a b, E₁ a b → E₁' a b)
    (h₂ : ∀ a b, E₂' a b → E₂ a b) : Step L' E₁' E₂' := by
  intro r m hm η hη hη1
  obtain ⟨n, k, hn, hk, hd, H⟩ := h r m hm η hη hη1
  refine ⟨n, k, hn, hk, hd, fun c hc => ?_⟩
  obtain ⟨φ, ⟨blk, f, z, hf, hcard, hφ⟩, hcφ⟩ := H c (fun x i a hxa => hc x i a (h₁ _ _ hxa))
  exact ⟨φ, ⟨blk, f, z, fun ℓ => hL _ (hf ℓ), hcard, hφ⟩,
    fun x i a hxa => hcφ x i a (h₂ _ _ hxa)⟩

end RamseyDisambig.Dev.DB.PartA
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {X : Type v}
alias Step_mono := RamseyDisambig.Dev.DB.PartA.Step_mono

/-! ## Part B: dense rotation systems (Theorem 19) -/
/-- Fill the gadget blocks `B b i` with the letters `v b i`, and `u` elsewhere. -/
noncomputable def fill (u : X) {m q n : ℕ} (B : Fin m → Fin (q + 1) → Finset (Fin n))
    (v : Fin m → Fin (q + 1) → X) : Fin n → X :=
  fun ℓ => if h : ∃ p : Fin m × Fin (q + 1), ℓ ∈ B p.1 p.2 then v h.choose.1 h.choose.2 else u

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartB
open RamseyDisambig.Dev.DB Classical
universe u v
variable {X : Type v}
/-- Generic fill: letters `x j` on the blocks `T j`, `u` elsewhere. -/
noncomputable def gw (u : X) {J ι : Type*} (T : J → Finset ι) (x : J → X) : ι → X :=
  fun ℓ => if h : ∃ j, ℓ ∈ T j then x h.choose else u

theorem gw_unique (u : X) {J ι : Type*} (T : J → Finset ι) (x : J → X) (y : ι → X)
    (h1 : ∀ j ℓ, ℓ ∈ T j → y ℓ = x j) (h2 : ∀ ℓ, (∀ j, ℓ ∉ T j) → y ℓ = u) :
    gw u T x = y := by
  funext ℓ
  unfold gw
  split_ifs with h
  · exact (h1 _ _ h.choose_spec).symm
  · push Not at h
    exact (h2 ℓ h).symm

theorem gw_mem (u : X) {J ι : Type*} (T : J → Finset ι) (x : J → X)
    (hT : ∀ j j', j ≠ j' → Disjoint (T j) (T j')) {j : J} {ℓ : ι} (hℓ : ℓ ∈ T j) :
    gw u T x ℓ = x j := by
  have h : ∃ j, ℓ ∈ T j := ⟨j, hℓ⟩
  unfold gw
  rw [dif_pos h]
  congr 1
  by_contra hne
  exact Finset.disjoint_left.mp (hT _ _ hne) h.choose_spec hℓ

theorem gw_not_mem (u : X) {J ι : Type*} (T : J → Finset ι) (x : J → X) {ℓ : ι}
    (hℓ : ∀ j, ℓ ∉ T j) : gw u T x ℓ = u := by
  unfold gw
  rw [dif_neg (by push Not; exact hℓ)]

theorem pair_disj {ι : Type*} {m q : ℕ} (B : Fin m → Fin (q + 1) → Finset ι)
    (h : ∀ b i b' i', (b, i) ≠ (b', i') → Disjoint (B b i) (B b' i')) :
    ∀ p p' : Fin m × Fin (q + 1), p ≠ p' → Disjoint (B p.1 p.2) (B p'.1 p'.2) :=
  fun p p' hne => h p.1 p.2 p'.1 p'.2 (by simpa using hne)

/-- The rotation-system property on an index type `ι`. -/
def RS (q s m r k : ℕ) (u : X) (ι : Type*) : Prop :=
  ∀ c : (Fin s → X) → (ι → X) → Fin r,
    ∃ B : Fin m → Fin (q + 1) → Finset ι,
      (∀ b i, (B b i).card = k) ∧
      (∀ b i b' i', (b, i) ≠ (b', i') → Disjoint (B b i) (B b' i')) ∧
      ∀ (w : Fin s → X) (v : Fin m → Fin (q + 1) → X) (b : Fin m),
        v b (Fin.last q) = u →
        c w (gw u (fun p : Fin m × Fin (q + 1) => B p.1 p.2) (fun p => v p.1 p.2)) =
          c w (gw u (fun p : Fin m × Fin (q + 1) => B p.1 p.2)
            (fun p => Function.update v b (fun i => v b (i - 1)) p.1 p.2))

theorem RS_equiv {q s m r k : ℕ} {u : X} {ι ι' : Type*} (e : ι ≃ ι')
    (h : RS q s m r k u ι) : RS (X := X) q s m r k u ι' := by
  intro c
  obtain ⟨B, hcard, hdis, hrot⟩ := h (fun w x => c w (x ∘ e.symm))
  refine ⟨fun b i => (B b i).map e.toEmbedding, ?_, ?_, ?_⟩
  · intro b i
    simp [hcard]
  · intro b i b' i' hne
    simpa [Finset.disjoint_map] using hdis b i b' i' hne
  · have key : ∀ v : Fin m → Fin (q + 1) → X,
        gw u (fun p : Fin m × Fin (q + 1) => (B p.1 p.2).map e.toEmbedding) (fun p => v p.1 p.2)
          = gw u (fun p : Fin m × Fin (q + 1) => B p.1 p.2) (fun p => v p.1 p.2) ∘ e.symm := by
      intro v
      apply gw_unique
      · intro p ℓ hℓ
        exact gw_mem u _ _ (pair_disj B hdis) (by simpa [Finset.mem_map_equiv] using hℓ)
      · intro ℓ hℓ
        apply gw_not_mem
        intro p hp
        exact hℓ p (by simpa [Finset.mem_map_equiv] using hp)
    intro w v b hv
    rw [key, key]
    exact hrot w v b hv

theorem RS_zero (q s r : ℕ) (u : X) : RS (X := X) q s 0 r 1 u (Fin 0) := by
  intro c
  exact ⟨fun b => Fin.elim0 b, fun b => Fin.elim0 b, fun b => Fin.elim0 b,
    fun _ _ b => Fin.elim0 b⟩

theorem fin_succ_sub_one {q : ℕ} (i : Fin q) :
    (Fin.succ i : Fin (q + 1)) - 1 = Fin.castSucc i := by
  rw [sub_eq_iff_eq_add, Fin.coeSucc_eq_succ]

theorem fin_zero_sub_one (q : ℕ) : (0 : Fin (q + 1)) - 1 = Fin.last q := by
  rw [sub_eq_iff_eq_add, Fin.last_add_one]

theorem update_castSucc {m q : ℕ} (v : Fin (m + 1) → Fin (q + 1) → X) (b : Fin m)
    (f : Fin (q + 1) → X) (p : Fin m) :
    Function.update v (Fin.castSucc b) f (Fin.castSucc p) =
      Function.update (fun x => v (Fin.castSucc x)) b f p := by
  by_cases h : p = b
  · subst h; simp
  · rw [Function.update_of_ne (fun h' => h (Fin.castSucc_injective _ h')),
      Function.update_of_ne h]

/-- Inflated inner word next to the new-region word. -/
def word {ι₀ : Type*} {a N : ℕ} (y : ι₀ → X) (z : Fin N → X) : (ι₀ × Fin a) ⊕ Fin N → X :=
  Sum.elim (fun p => y p.1) z

theorem RS_step (q : ℕ) (u : X) (s m r k₀ a N : ℕ) {ι₀ : Type*}
    (hin : RS (X := X) q (s + (q + 1)) m r k₀ u ι₀) (C R : ℕ)
    (eP : ((Fin s → X) → (ι₀ → X) → (Fin q → X) → Fin r) ≃ Fin R)
    (hC : ∀ n k : ℕ, (q + 1) * k + C ≤ n →
      ∀ c : (Fin q → Finset (Fin n)) → Fin R,
        ∃ A : Fin (q + 1) → Finset (Fin n),
          (∀ i, (A i).card = k) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
            c (fun i => A i.castSucc) = c (fun i => A i.succ))
    (hN : (q + 1) * (k₀ * a) + C ≤ N) :
    RS (X := X) q s (m + 1) r (k₀ * a) u ((ι₀ × Fin a) ⊕ Fin N) := by
  intro c
  let P := (Fin s → X) → (ι₀ → X) → (Fin q → X) → Fin r
  let prof : (Fin q → Finset (Fin N)) → P :=
    fun T w y x => c w (word (a := a) y (gw u T x))
  obtain ⟨A, hAc, hAd, hAe⟩ := hC N (k₀ * a) hN (fun T => eP (prof T))
  have hAe' := eP.injective hAe
  obtain ⟨Bi, hBc, hBd, hBr⟩ := hin (fun w' y => c (fun i => w' (Fin.castAdd (q + 1) i))
      (word (a := a) y (gw u A (fun i => w' (Fin.natAdd s i)))))
  let B : Fin (m + 1) → Fin (q + 1) → Finset ((ι₀ × Fin a) ⊕ Fin N) :=
    fun b => Fin.lastCases (motive := fun _ => Fin (q + 1) → Finset ((ι₀ × Fin a) ⊕ Fin N))
      (fun i => (A i).map Function.Embedding.inr)
      (fun b' i => ((Bi b' i) ×ˢ (Finset.univ : Finset (Fin a))).map Function.Embedding.inl) b
  have hBl : ∀ i, B (Fin.last m) i = (A i).map Function.Embedding.inr := by
    intro i; simp [B]
  have hBs : ∀ b' i, B (Fin.castSucc b') i =
      ((Bi b' i) ×ˢ (Finset.univ : Finset (Fin a))).map Function.Embedding.inl := by
    intro b' i; simp [B]
  have hfill : ∀ v : Fin (m + 1) → Fin (q + 1) → X,
      gw u (fun p : Fin (m + 1) × Fin (q + 1) => B p.1 p.2) (fun p => v p.1 p.2) =
        word (gw u (fun p : Fin m × Fin (q + 1) => Bi p.1 p.2)
          (fun p => v (Fin.castSucc p.1) p.2)) (gw u A (v (Fin.last m))) := by
    intro v
    apply gw_unique
    · rintro ⟨b, i⟩ ℓ hℓ
      induction b using Fin.lastCases with
      | last =>
        rw [hBl] at hℓ
        obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hℓ
        exact gw_mem u A _ hAd ht
      | cast b' =>
        rw [hBs] at hℓ
        obtain ⟨⟨p, t⟩, hpt, rfl⟩ := Finset.mem_map.mp hℓ
        have hp : p ∈ Bi b' i := (Finset.mem_product.mp hpt).1
        simp only [word, Function.Embedding.inl_apply, Sum.elim_inl]
        exact gw_mem u (fun p : Fin m × Fin (q + 1) => Bi p.1 p.2) _ (pair_disj Bi hBd)
          (j := (b', i)) hp
    · intro ℓ hℓ
      rcases ℓ with ⟨p, t⟩ | t
      · simp only [word, Sum.elim_inl]
        apply gw_not_mem
        rintro ⟨b', i⟩ hp
        apply hℓ (Fin.castSucc b', i)
        rw [hBs]
        exact Finset.mem_map_of_mem _ (Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩)
      · apply gw_not_mem
        intro i ht
        apply hℓ (Fin.last m, i)
        rw [hBl]
        exact Finset.mem_map_of_mem _ ht
  refine ⟨B, ?_, ?_, ?_⟩
  · intro b i
    induction b using Fin.lastCases with
    | last => rw [hBl, Finset.card_map, hAc]
    | cast b' => rw [hBs, Finset.card_map, Finset.card_product, hBc, Finset.card_univ,
        Fintype.card_fin]
  · intro b i b' i' hne
    induction b using Fin.lastCases with
    | last =>
      induction b' using Fin.lastCases with
      | last =>
        rw [hBl, hBl, Finset.disjoint_map]
        exact hAd i i' (fun h => hne (by rw [h]))
      | cast b'' =>
        rw [hBl, hBs, Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨t', -, ht'⟩ := Finset.mem_map.mp hx'
        simp at ht'
    | cast b₁ =>
      induction b' using Fin.lastCases with
      | last =>
        rw [hBl, hBs, Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨t', -, ht'⟩ := Finset.mem_map.mp hx'
        simp at ht'
      | cast b'' =>
        rw [hBs, hBs, Finset.disjoint_map]
        apply Finset.disjoint_product.mpr
        left
        apply hBd
        intro h
        apply hne
        simp only [Prod.mk.injEq] at h ⊢
        exact ⟨by rw [h.1], h.2⟩
  · intro w v b hv
    rw [hfill, hfill]
    induction b using Fin.lastCases with
    | last =>
      have hv1 : (fun p : Fin m × Fin (q + 1) =>
          Function.update v (Fin.last m) (fun i => v (Fin.last m) (i - 1))
            (Fin.castSucc p.1) p.2) = fun p => v (Fin.castSucc p.1) p.2 := by
        funext p
        rw [Function.update_of_ne (Fin.castSucc_lt_last p.1).ne]
      rw [hv1, Function.update_self]
      set Y := gw u (fun p : Fin m × Fin (q + 1) => Bi p.1 p.2)
        (fun p => v (Fin.castSucc p.1) p.2)
      have hx := congrFun (congrFun (congrFun hAe' w) Y)
        (fun i => v (Fin.last m) (Fin.castSucc i))
      have hdc : ∀ i j : Fin q, i ≠ j → Disjoint (A i.castSucc) (A j.castSucc) :=
        fun i j h => hAd _ _ (fun h' => h (Fin.castSucc_injective _ h'))
      have hds : ∀ i j : Fin q, i ≠ j → Disjoint (A i.succ) (A j.succ) :=
        fun i j h => hAd _ _ (fun h' => h (Fin.succ_injective _ h'))
      have e1 : gw u (fun i => A i.castSucc) (fun i => v (Fin.last m) (Fin.castSucc i)) =
          gw u A (v (Fin.last m)) := by
        apply gw_unique
        · intro i ℓ hℓ
          exact gw_mem u A _ hAd hℓ
        · intro ℓ hℓ
          by_cases h : ∃ j, ℓ ∈ A j
          · obtain ⟨j, hj⟩ := h
            induction j using Fin.lastCases with
            | last => rw [gw_mem u A _ hAd hj, hv]
            | cast i => exact absurd hj (hℓ i)
          · push Not at h
            exact gw_not_mem u A _ h
      have e2 : gw u (fun i => A i.succ) (fun i => v (Fin.last m) (Fin.castSucc i)) =
          gw u A (fun i => v (Fin.last m) (i - 1)) := by
        apply gw_unique
        · intro i ℓ hℓ
          rw [gw_mem u A _ hAd hℓ, fin_succ_sub_one]
        · intro ℓ hℓ
          by_cases h : ∃ j, ℓ ∈ A j
          · obtain ⟨j, hj⟩ := h
            induction j using Fin.cases with
            | zero => rw [gw_mem u A _ hAd hj, fin_zero_sub_one, hv]
            | succ i => exact absurd hj (hℓ i)
          · push Not at h
            exact gw_not_mem u A _ h
      rw [← e1, ← e2]
      exact hx
    | cast b' =>
      have hl : Function.update v (Fin.castSucc b') (fun i => v (Fin.castSucc b') (i - 1))
          (Fin.last m) = v (Fin.last m) :=
        Function.update_of_ne (Fin.castSucc_lt_last b').ne' _ _
      rw [hl]
      simp only [update_castSucc]
      have := hBr (Fin.append w (v (Fin.last m))) (fun p => v (Fin.castSucc p)) b' hv
      simp only [Fin.append_left, Fin.append_right] at this
      exact this

theorem RS_main [Fintype X] (q : ℕ) (hp : (q + 1).Prime) (u : X) (r : ℕ) (η : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (m : ℕ) :
    ∀ s : ℕ, ∃ n k : ℕ, 1 ≤ k ∧ m * (q + 1) * k ≤ n ∧
      (1 - η) * (n : ℝ) ≤ (m : ℝ) * ((q + 1 : ℕ) : ℝ) * (k : ℝ) ∧
        RS (X := X) q s m r k u (Fin n) := by
  induction m with
  | zero => intro s; exact ⟨0, 1, le_rfl, by simp, by simp, RS_zero q s r u⟩
  | succ m ih =>
    intro s
    obtain ⟨n₀, k₀, hk₀, hmn, hdens, hRS⟩ := ih (s + (q + 1))
    obtain ⟨C, hC⟩ := Palvolgyi2026.kneser_shift q hp
      (Fintype.card ((Fin s → X) → (Fin n₀ → X) → (Fin q → X) → Fin r))
    set a := ⌈(C : ℝ) / η⌉₊ + 1 with ha
    refine ⟨n₀ * a + ((q + 1) * (k₀ * a) + C), k₀ * a, ?_, ?_, ?_, ?_⟩
    · exact Nat.mul_pos hk₀ (Nat.succ_pos _)
    · have := Nat.mul_le_mul_right a hmn
      nlinarith
    · have hCa : (C : ℝ) ≤ η * a := by
        have h1 : (C : ℝ) / η ≤ a := by
          rw [ha]; push_cast
          linarith [Nat.le_ceil ((C : ℝ) / η)]
        rw [div_le_iff₀ hη] at h1
        linarith
      have hk1 : (1 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
      have ha0 : (0 : ℝ) ≤ a := by positivity
      push_cast at hdens ⊢
      have h2 : (1 - η) * n₀ * a ≤ m * (q + 1) * k₀ * a := mul_le_mul_of_nonneg_right hdens ha0
      have h3 : η * a ≤ η * ((q + 1) * k₀ * a) := by
        apply mul_le_mul_of_nonneg_left _ hη.le
        have : (1 : ℝ) ≤ (q + 1) * k₀ := by nlinarith
        nlinarith
      have hC0 : (0 : ℝ) ≤ C := by positivity
      nlinarith
    · have hst : RS (X := X) q s (m + 1) r (k₀ * a) u
          ((Fin n₀ × Fin a) ⊕ Fin ((q + 1) * (k₀ * a) + C)) :=
        RS_step q u s m r k₀ a _ hRS C _ (Fintype.equivFin _) hC le_rfl
      have e : ((Fin n₀ × Fin a) ⊕ Fin ((q + 1) * (k₀ * a) + C)) ≃
          Fin (n₀ * a + ((q + 1) * (k₀ * a) + C)) :=
        (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv
      exact RS_equiv e hst

end RamseyDisambig.Dev.DB.PartB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartB
open RamseyDisambig.Dev.DB Classical
universe u v
theorem fill_eq_gw {X : Type v} (u : X) {m q n : ℕ} (B : Fin m → Fin (q + 1) → Finset (Fin n))
    (v : Fin m → Fin (q + 1) → X) :
    fill u B v = gw u (fun p : Fin m × Fin (q + 1) => B p.1 p.2) (fun p => v p.1 p.2) := by
  funext ℓ
  unfold fill gw
  split_ifs <;> rfl

theorem rotation_system {X : Type v} (q : ℕ) (hp : (q + 1).Prime) [Fintype X] (u : X) (s m r : ℕ)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ n k : ℕ, 1 ≤ k ∧ m * (q + 1) * k ≤ n ∧
      (1 - η) * (n : ℝ) ≤ (m : ℝ) * ((q + 1 : ℕ) : ℝ) * (k : ℝ) ∧
      ∀ c : (Fin s → X) → (Fin n → X) → Fin r,
        ∃ B : Fin m → Fin (q + 1) → Finset (Fin n),
          (∀ b i, (B b i).card = k) ∧
          (∀ b i b' i', (b, i) ≠ (b', i') → Disjoint (B b i) (B b' i')) ∧
          ∀ (w : Fin s → X) (v : Fin m → Fin (q + 1) → X) (b : Fin m),
            v b (Fin.last q) = u →
            c w (fill u B v) = c w (fill u B (Function.update v b (fun i => v b (i - 1)))) := by
  obtain ⟨n, k, h1, h2, h3, h4⟩ := RS_main q hp u r η hη hη1 m s
  refine ⟨n, k, h1, h2, h3, fun c => ?_⟩
  obtain ⟨B, hc, hd, hr⟩ := h4 c
  refine ⟨B, hc, hd, fun w v b hv => ?_⟩
  rw [fill_eq_gw, fill_eq_gw]
  exact hr w v b hv

end RamseyDisambig.Dev.DB.PartB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {X : Type v}
alias rotation_system := RamseyDisambig.Dev.DB.PartB.rotation_system

/-! ## Part C: one-orbit fusion and prime cyclic actions -/
/-- Labels of a cyclic block map: powers of `τ`. -/
def LPow (τ : Equiv.Perm X) (f : X → X) : Prop := ∃ e : ℕ, f = ⇑(τ ^ e)

/-- `a` and `b` both lie in `{y, τ y, …, τ^(t-1) y}`. -/
def Seg (τ : Equiv.Perm X) (t : ℕ) (y : X) (a b : X) : Prop :=
  (∃ i < t, a = (τ ^ i) y) ∧ (∃ i < t, b = (τ ^ i) y)

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartC
open RamseyDisambig.Dev.DB Classical
universe u v
variable {X : Type v}
theorem fill_choose_eq {m q n : ℕ} {B : Fin m → Fin (q + 1) → Finset (Fin n)}
    (hB : ∀ b i b' i', (b, i) ≠ (b', i') → Disjoint (B b i) (B b' i'))
    {ℓ : Fin n} (h : ∃ p : Fin m × Fin (q + 1), ℓ ∈ B p.1 p.2) {b : Fin m} {i : Fin (q + 1)}
    (hℓ : ℓ ∈ B b i) : h.choose = (b, i) := by
  by_contra hne
  exact Finset.disjoint_left.1 (hB h.choose.1 h.choose.2 b i hne) h.choose_spec hℓ

theorem fill_rel (u : X) {m q n : ℕ} (B : Fin m → Fin (q + 1) → Finset (Fin n))
    (R : X → X → Prop) (v v' : Fin m → Fin (q + 1) → X)
    (h : ∀ b i, v b i = v' b i ∨ R (v b i) (v' b i)) (ℓ : Fin n) :
    fill u B v ℓ = fill u B v' ℓ ∨ R (fill u B v ℓ) (fill u B v' ℓ) := by
  unfold fill
  split_ifs with hh
  · exact h _ _
  · exact Or.inl rfl

theorem isBlk_fill (τ : Equiv.Perm X) (y : X) {m q n k₂ : ℕ}
    (B : Fin m → Fin (q + 1) → Finset (Fin n)) (hBc : ∀ b i, (B b i).card = k₂)
    (hBd : ∀ b i b' i', (b, i) ≠ (b', i') → Disjoint (B b i) (B b' i')) :
    IsBlk (LPow τ) m n ((q + 1) * k₂)
      (fun x => fill y B (fun b i => (τ ^ (i : ℕ)) (x b))) := by
  refine ⟨fun ℓ => if h : ∃ p : Fin m × Fin (q + 1), ℓ ∈ B p.1 p.2 then some h.choose.1 else none,
    fun ℓ => if h : ∃ p : Fin m × Fin (q + 1), ℓ ∈ B p.1 p.2 then ⇑(τ ^ (h.choose.2 : ℕ))
      else ⇑(τ ^ 0), fun _ => y, ?_, ?_, ?_⟩
  · intro ℓ
    dsimp only
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · intro j
    have hfil : (Finset.univ.filter (fun ℓ =>
        (if h : ∃ p : Fin m × Fin (q + 1), ℓ ∈ B p.1 p.2 then some h.choose.1 else none) = some j))
        = Finset.univ.biUnion (fun i => B j i) := by
      ext ℓ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro H
        split_ifs at H with h
        · have hj : h.choose.1 = j := Option.some_injective _ H
          exact ⟨h.choose.2, hj ▸ h.choose_spec⟩
      · rintro ⟨i, hi⟩
        have h : ∃ p : Fin m × Fin (q + 1), ℓ ∈ B p.1 p.2 := ⟨(j, i), hi⟩
        rw [dif_pos h, fill_choose_eq hBd h hi]
    rw [hfil, Finset.card_biUnion]
    · simp [hBc]
    · intro i _ i' _ hii'
      exact hBd j i j i' (by simp [hii'])
  · intro x ℓ
    simp only [fill]
    split_ifs with h
    · rfl
    · rfl

theorem E_pow {τ : Equiv.Perm X} {E : X → X → Prop} (hE : ∀ a b, E a b → E (τ a) (τ b)) :
    ∀ (e : ℕ) (a b : X), E a b → E ((τ ^ e) a) ((τ ^ e) b)
  | 0, a, b, h => by simpa using h
  | e + 1, a, b, h => by
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact hE _ _ (E_pow hE e a b h)

theorem exp_in {τ : Equiv.Perm X} {q : ℕ} (hτ : τ ^ (q + 1) = 1) (y : X) {t e : ℕ}
    (h : e < t ∨ (q + 1 ≤ e ∧ e < q + 1 + t)) : ∃ j < t, (τ ^ e) y = (τ ^ j) y := by
  rcases h with h | ⟨h1, h2⟩
  · exact ⟨e, h, rfl⟩
  · refine ⟨e - (q + 1), by omega, ?_⟩
    conv_lhs => rw [show e = (e - (q + 1)) + (q + 1) by omega, pow_add, hτ, mul_one]

/-- The shifted word used in the U,V calculation (`V` of the paper, 0-indexed). -/
def Vw (τ : Equiv.Perm X) (y : X) (q i : ℕ) : Fin (q + 1) → X :=
  fun l => if (l : ℕ) + i < q + 1 then (τ ^ (i + (l : ℕ))) y else y

theorem core {β : Type*} (τ : Equiv.Perm X) {q : ℕ} (hτ : τ ^ (q + 1) = 1) (y : X) {t : ℕ}
    (ht : 1 ≤ t) {m : ℕ} (G : (Fin m → Fin (q + 1) → X) → β)
    (ha : ∀ v v' : Fin m → Fin (q + 1) → X,
      (∀ b i, v b i = v' b i ∨ Seg τ t y (v b i) (v' b i)) → G v = G v')
    (hb : ∀ (v : Fin m → Fin (q + 1) → X) (b : Fin m), v b (Fin.last q) = y →
      G v = G (Function.update v b (fun i => v b (i - 1))))
    (v : Fin m → Fin (q + 1) → X) (b : Fin m) :
    ∀ j ≤ t, G (Function.update v b (fun l => (τ ^ (j + (l : ℕ))) y)) =
      G (Function.update v b (fun l => (τ ^ (0 + (l : ℕ))) y)) := by
  have hupd : ∀ w w' : Fin (q + 1) → X, (∀ l, w l = w' l ∨ Seg τ t y (w l) (w' l)) →
      G (Function.update v b w) = G (Function.update v b w') := by
    intro w w' h
    apply ha
    intro b' i
    by_cases hb' : b' = b
    · subst hb'
      simpa using h i
    · simp [Function.update_of_ne hb']
  have hy : ∃ j < t, y = (τ ^ j) y := ⟨0, by omega, by simp⟩
  have step : ∀ i, 1 ≤ i → i ≤ t →
      G (Function.update v b (fun l => (τ ^ ((i - 1) + (l : ℕ))) y)) =
        G (Function.update v b (fun l => (τ ^ (i + (l : ℕ))) y)) := by
    intro i hi1 hit
    have h1 : G (Function.update v b (fun l => (τ ^ ((i - 1) + (l : ℕ))) y)) =
        G (Function.update v b (fun l => Vw τ y q i (l - 1))) := by
      apply hupd
      intro l
      have hl' := Fin.coe_sub_one l
      have hlt := l.isLt
      unfold Vw
      by_cases hl : l = 0
      · rw [if_pos hl] at hl'
        rw [hl', if_neg (by omega)]
        right
        refine ⟨exp_in hτ y (Or.inl (by subst hl; simp; omega)), hy⟩
      · rw [if_neg hl] at hl'
        have hlpos : 0 < (l : ℕ) := by
          rcases Nat.eq_zero_or_pos (l : ℕ) with h0 | h0
          · exact absurd (Fin.ext h0) hl
          · exact h0
        rw [hl']
        split_ifs with hc
        · left
          congr 2
          omega
        · right
          exact ⟨exp_in hτ y (Or.inr ⟨by omega, by omega⟩), hy⟩
    have h2 : G (Function.update v b (fun l => Vw τ y q i (l - 1))) =
        G (Function.update v b (Vw τ y q i)) := by
      have hlast : (Function.update v b (Vw τ y q i)) b (Fin.last q) = y := by
        rw [Function.update_self]
        unfold Vw
        rw [if_neg (by simp; omega)]
      have := hb _ b hlast
      simp only [Function.update_self, Function.update_idem] at this
      exact this.symm
    have h3 : G (Function.update v b (Vw τ y q i)) =
        G (Function.update v b (fun l => (τ ^ (i + (l : ℕ))) y)) := by
      apply hupd
      intro l
      have hlt := l.isLt
      unfold Vw
      split_ifs with hc
      · exact Or.inl rfl
      · right
        exact ⟨hy, exp_in hτ y (Or.inr ⟨by omega, by omega⟩)⟩
    rw [h1, h2, h3]
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    have := step (j + 1) (by omega) hj
    simp only [Nat.add_sub_cancel] at this
    rw [← this]
    exact ih (by omega)

theorem fusion_step (q : ℕ) (hp : (q + 1).Prime) [Fintype X] (τ : Equiv.Perm X)
    (hτ : τ ^ (q + 1) = 1) (E : X → X → Prop) (hE : ∀ a b, E a b → E (τ a) (τ b)) (y : X)
    (t : ℕ) (ht : 1 ≤ t) (htq : t ≤ q) :
    Step (LPow τ) (fun a b => E a b ∨ Seg τ t y a b) (fun a b => E a b ∨ Seg τ (t + 1) y a b) := by
  intro r m hm η hη hη1
  obtain ⟨n, k₂, hk₂, hn, hdens, hrot⟩ := rotation_system q hp y 0 m r η hη hη1
  have hpos : 0 < m * (q + 1) * k₂ := Nat.mul_pos (Nat.mul_pos hm (Nat.succ_pos q)) hk₂
  refine ⟨n, (q + 1) * k₂, by omega, Nat.mul_pos (Nat.succ_pos q) hk₂, ?_, ?_⟩
  · calc (1 - η) * (n : ℝ) ≤ (m : ℝ) * ((q + 1 : ℕ) : ℝ) * (k₂ : ℝ) := hdens
      _ = (m : ℝ) * (((q + 1) * k₂ : ℕ) : ℝ) := by push_cast; ring
  intro c hc
  obtain ⟨B, hBc, hBd, hBr⟩ := hrot (fun _ w => c w)
  have hblk := isBlk_fill τ y B hBc hBd
  refine ⟨_, hblk, ?_⟩
  intro x b a hxa
  rcases hxa with hEa | hS
  · have hE' : ∀ f, LPow τ f → ∀ a b, E a b → E (f a) (f b) := by
      rintro f ⟨e, rfl⟩ a b h
      exact E_pow hE e a b h
    exact Ins_comp hE' hblk (fun x i a h => hc x i a (Or.inl h)) x b a hEa
  · obtain ⟨⟨i, hi, hxi⟩, ⟨j, hj, haj⟩⟩ := hS
    let G : (Fin m → Fin (q + 1) → X) → Fin r := fun w => c (fill y B w)
    let v : Fin m → Fin (q + 1) → X := fun b' l => (τ ^ (l : ℕ)) (x b')
    have ha : ∀ w w' : Fin m → Fin (q + 1) → X,
        (∀ b i, w b i = w' b i ∨ Seg τ t y (w b i) (w' b i)) → G w = G w' := by
      intro w w' h
      apply Ins_congr hc
      intro ℓ
      rcases fill_rel y B (Seg τ t y) w w' h ℓ with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    have hb : ∀ (w : Fin m → Fin (q + 1) → X) (b : Fin m), w b (Fin.last q) = y →
        G w = G (Function.update w b (fun i => w b (i - 1))) :=
      fun w b h => hBr (fun i => i.elim0) w b h
    have key : ∀ e : ℕ, c (fill y B (fun b' l => (τ ^ (l : ℕ)) (Function.update x b ((τ ^ e) y) b')))
        = G (Function.update v b (fun l => (τ ^ (e + (l : ℕ))) y)) := by
      intro e
      show c _ = c _
      congr 2
      funext b' l
      by_cases h : b' = b
      · subst h
        simp only [Function.update_self]
        rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
      · simp only [Function.update_of_ne h, v]
    have hc0 := core τ hτ y ht G ha hb v b
    show c _ = c _
    calc c (fill y B (fun b' l => (τ ^ (l : ℕ)) (x b')))
        = c (fill y B (fun b' l => (τ ^ (l : ℕ)) (Function.update x b ((τ ^ i) y) b'))) := by
          rw [← hxi, Function.update_eq_self]
      _ = G (Function.update v b (fun l => (τ ^ (i + (l : ℕ))) y)) := key i
      _ = G (Function.update v b (fun l => (τ ^ (0 + (l : ℕ))) y)) := hc0 i (by omega)
      _ = G (Function.update v b (fun l => (τ ^ (j + (l : ℕ))) y)) := (hc0 j (by omega)).symm
      _ = c (fill y B (fun b' l => (τ ^ (l : ℕ)) (Function.update x b ((τ ^ j) y) b'))) :=
          (key j).symm
      _ = c (fill y B (fun b' l => (τ ^ (l : ℕ)) (Function.update x b a b'))) := by rw [← haj]

end RamseyDisambig.Dev.DB.PartC
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {X : Type v}

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartC
open RamseyDisambig.Dev.DB Classical
universe u v
variable {X : Type v}
/-- Relation after the orbits through `S` have been fused. -/
def ES (τ : Equiv.Perm X) (q : ℕ) (S : Finset X) (a b : X) : Prop :=
  a = b ∨ ∃ y ∈ S, Seg τ (q + 1) y a b

theorem LPow_comp (τ : Equiv.Perm X) : ∀ f g, LPow τ f → LPow τ g → LPow τ (f ∘ g) := by
  rintro f g ⟨a, rfl⟩ ⟨b, rfl⟩
  exact ⟨a + b, by rw [pow_add, Equiv.Perm.coe_mul]⟩

theorem LPow_id (τ : Equiv.Perm X) : LPow τ id := ⟨0, by simp⟩

theorem ES_inv {τ : Equiv.Perm X} {q : ℕ} (hτ : τ ^ (q + 1) = 1) (S : Finset X) :
    ∀ a b, ES τ q S a b → ES τ q S (τ a) (τ b) := by
  rintro a b (rfl | ⟨y, hy, ⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩)
  · exact Or.inl rfl
  · refine Or.inr ⟨y, hy, ⟨(i + 1) % (q + 1), Nat.mod_lt _ (by omega), ?_⟩,
      ⟨(j + 1) % (q + 1), Nat.mod_lt _ (by omega), ?_⟩⟩
    · rw [← pow_eq_pow_mod _ hτ, pow_succ', Equiv.Perm.mul_apply]
    · rw [← pow_eq_pow_mod _ hτ, pow_succ', Equiv.Perm.mul_apply]

theorem seg_chain (q : ℕ) (hp : (q + 1).Prime) [Fintype X] [Nonempty X] (τ : Equiv.Perm X)
    (hτ : τ ^ (q + 1) = 1) (S : Finset X) (y : X) :
    ∀ t, 1 ≤ t → t ≤ q + 1 →
      Step (LPow τ) (ES τ q S) (fun a b => ES τ q S a b ∨ Seg τ t y a b) := by
  intro t ht htq
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · refine Step_mono (Step_refl (LPow_id τ) (ES τ q S)) (fun f h => h) (fun a b h => h) ?_
      rintro a b (h | ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩)
      · exact h
      · obtain rfl : i = 0 := by omega
        obtain rfl : j = 0 := by omega
        exact Or.inl rfl
    · exact Step_trans (LPow_comp τ) (ih htpos (by omega))
        (fusion_step q hp τ hτ (ES τ q S) (ES_inv hτ S) y t htpos (by omega))

theorem cyclic_step (q : ℕ) (hp : (q + 1).Prime) [Fintype X] [Nonempty X] (τ : Equiv.Perm X)
    (hτ : τ ^ (q + 1) = 1) :
    Step (LPow τ) (fun a b => a = b) (fun a b => ∃ e : ℕ, b = (τ ^ e) a) := by
  have key : ∀ S : Finset X, Step (LPow τ) (fun a b => a = b) (ES τ q S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine Step_mono (Step_refl (LPow_id τ) _) (fun f h => h) (fun a b h => h) ?_
      rintro a b (h | ⟨y, hy, -⟩)
      · exact h
      · simp at hy
    | @insert y S hyS ih =>
      refine Step_trans (LPow_comp τ) ih (Step_mono (seg_chain q hp τ hτ S y (q + 1) (by omega)
        le_rfl) (fun f h => h) (fun a b h => h) ?_)
      rintro a b (h | ⟨z, hz, hseg⟩)
      · exact Or.inl (Or.inl h)
      · rcases Finset.mem_insert.1 hz with rfl | hz
        · exact Or.inr hseg
        · exact Or.inl (Or.inr ⟨z, hz, hseg⟩)
  refine Step_mono (key Finset.univ) (fun f h => h) (fun a b h => h) ?_
  rintro a b ⟨e, rfl⟩
  exact Or.inr ⟨a, Finset.mem_univ _, ⟨0, by omega, by simp⟩,
    ⟨e % (q + 1), Nat.mod_lt _ (by omega), by rw [← pow_eq_pow_mod _ hτ]⟩⟩

end RamseyDisambig.Dev.DB.PartC
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {X : Type v}
alias cyclic_step := RamseyDisambig.Dev.DB.PartC.cyclic_step

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
/-! ## Part D: prime cyclic extensions and solvable groups -/
/-- Labels from a subgroup. -/
def LSub (K : Subgroup G) (f : X → X) : Prop := ∃ a ∈ K, f = fun x => a • x

/-- Orbit relation of a subgroup. -/
def OSub (K : Subgroup G) (a b : X) : Prop := ∃ κ ∈ K, b = κ • a

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartD
open RamseyDisambig.Dev.DB Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
theorem ins_eq_all {ι : Type*} [DecidableEq ι] {β : Type*} (g : (ι → X) → β) :
    Ins (fun a b : X => a = b) g := by
  intro x i a h; subst h; simp

theorem dens_comb {η : ℝ} (hη : 0 < η) (hη1 : η < 1) {n n₀ m k₁ k₂ : ℕ}
    (h₁ : (1 - η / 2) * (n : ℝ) ≤ (n₀ : ℝ) * (k₁ : ℝ))
    (h₂ : (1 - η / 2) * (n₀ : ℝ) ≤ (m : ℝ) * (k₂ : ℝ)) :
    (1 - η) * (n : ℝ) ≤ (m : ℝ) * ((k₁ * k₂ : ℕ) : ℝ) := by
  push_cast
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk : (0 : ℝ) ≤ k₁ := Nat.cast_nonneg k₁
  have ha : 0 ≤ 1 - η / 2 := by linarith
  have e1 : (1 - η) * (n : ℝ) ≤ (1 - η / 2) * ((1 - η / 2) * n) := by
    nlinarith [mul_nonneg (sq_nonneg η) hn]
  have e2 : (1 - η / 2) * ((1 - η / 2) * n) ≤ (1 - η / 2) * (n₀ * k₁) :=
    mul_le_mul_of_nonneg_left h₁ ha
  have e3 : (1 - η / 2) * (n₀ * k₁) ≤ m * k₂ * k₁ := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h₂ hk
  nlinarith

/-- The orbit setoid of a subgroup. -/
def osetoid (K' : Subgroup G) : Setoid X where
  r := OSub K'
  iseqv := ⟨fun a => ⟨1, K'.one_mem, (one_smul G a).symm⟩,
    fun ⟨κ, hκ, h⟩ => ⟨κ⁻¹, K'.inv_mem hκ, by rw [h, inv_smul_smul]⟩,
    fun ⟨κ, hκ, h⟩ ⟨κ', hκ', h'⟩ => ⟨κ' * κ, K'.mul_mem hκ' hκ, by rw [h', h, mul_smul]⟩⟩

theorem osub_smul {K' : Subgroup G} {g : G} (hg : ∀ a ∈ K', g * a * g⁻¹ ∈ K') {a b : X}
    (h : OSub K' a b) : OSub K' (g • a) (g • b) := by
  obtain ⟨κ, hκ, rfl⟩ := h
  exact ⟨g * κ * g⁻¹, hg κ hκ, by simp [mul_smul]⟩

/-- The induced map on orbits of `K'`. -/
def qact (K' : Subgroup G) (g : G) (hg : ∀ a ∈ K', g * a * g⁻¹ ∈ K') :
    Quotient (osetoid (X := X) K') → Quotient (osetoid (X := X) K') :=
  Quotient.lift (fun a => Quotient.mk (osetoid K') (g • a))
    (fun _ _ h => Quotient.sound (osub_smul hg h))

/-- The induced permutation of orbits of `K'`. -/
def qperm (K' : Subgroup G) (g : G) (hg : ∀ a ∈ K', g * a * g⁻¹ ∈ K')
    (hg' : ∀ a ∈ K', g⁻¹ * a * g⁻¹⁻¹ ∈ K') : Equiv.Perm (Quotient (osetoid (X := X) K')) where
  toFun := qact K' g hg
  invFun := qact K' g⁻¹ hg'
  left_inv := fun x => Quotient.inductionOn x (fun a => by
    show Quotient.mk _ (g⁻¹ • g • a) = _
    rw [inv_smul_smul])
  right_inv := fun x => Quotient.inductionOn x (fun a => by
    show Quotient.mk _ (g • g⁻¹ • a) = _
    rw [smul_inv_smul])

theorem qperm_pow (K' : Subgroup G) (g : G) (hg : ∀ a ∈ K', g * a * g⁻¹ ∈ K')
    (hg' : ∀ a ∈ K', g⁻¹ * a * g⁻¹⁻¹ ∈ K') (e : ℕ) (a : X) :
    (qperm K' g hg hg' ^ e) (Quotient.mk (osetoid K') a) = Quotient.mk (osetoid K') (g ^ e • a) := by
  induction e generalizing a with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, Equiv.Perm.mul_apply]
    show (qperm K' g hg hg' ^ e) (Quotient.mk _ (g • a)) = _
    rw [ih, pow_succ, mul_smul]

/-- Proposition 24 (extension step), with subgroups of an ambient group. -/
theorem extension_step [Finite X] [Nonempty X] (K' K : Subgroup G) (hle : K' ≤ K)
    (hnorm : ∀ κ ∈ K, ∀ a ∈ K', κ * a * κ⁻¹ ∈ K') (g : G) (hg : g ∈ K) (q : ℕ)
    (hp : (q + 1).Prime) (hgp : g ^ (q + 1) ∈ K') (hcov : ∀ κ ∈ K, ∃ e : ℕ, κ * (g ^ e)⁻¹ ∈ K')
    (h : Step (LSub (X := X) K') (fun a b => a = b) (OSub K')) :
    Step (LSub (X := X) K) (fun a b => a = b) (OSub K) := by
  have : Fintype (Quotient (osetoid (X := X) K')) := Fintype.ofFinite _
  have : Nonempty (Quotient (osetoid (X := X) K')) :=
    ⟨Quotient.mk (osetoid K') (Classical.arbitrary X)⟩
  have hτe := qperm_pow (X := X) K' g (hnorm g hg) (hnorm g⁻¹ (K.inv_mem hg))
  set τ := qperm (X := X) K' g (hnorm g hg) (hnorm g⁻¹ (K.inv_mem hg)) with hτdef
  have hτ : τ ^ (q + 1) = 1 := by
    ext x
    induction x using Quotient.inductionOn with
    | h a =>
      rw [hτe, Equiv.Perm.one_apply]
      exact Quotient.sound ⟨(g ^ (q + 1))⁻¹, K'.inv_mem hgp, by simp⟩
  have hLK : ∀ f₁ f₂ : X → X, LSub K f₁ → LSub K f₂ → LSub K (f₁ ∘ f₂) := by
    rintro f₁ f₂ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, K.mul_mem ha hb, by funext x; simp [mul_smul]⟩
  intro r m hm η hη hη1
  obtain ⟨n₀, k₂, hn₀, hk₂, hd₂, H₂⟩ :=
    cyclic_step q hp τ hτ r m hm (η / 2) (by linarith) (by linarith)
  obtain ⟨n, k₁, hn, hk₁, hd₁, H₁⟩ := h r n₀ hn₀ (η / 2) (by linarith) (by linarith)
  refine ⟨n, k₁ * k₂, hn, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    dens_comb hη hη1 hd₁ hd₂, fun c hc => ?_⟩
  obtain ⟨Φ, hΦ, hcΦ⟩ := H₁ c hc
  have hΦK : IsBlk (LSub (X := X) K) n₀ n k₁ Φ := by
    obtain ⟨blk, f, z, hf, hcard, hφ⟩ := hΦ
    exact ⟨blk, f, z, fun ℓ => by
      obtain ⟨a, ha, hfa⟩ := hf ℓ
      exact ⟨a, hle ha, hfa⟩, hcard, hφ⟩
  let cb : (Fin n₀ → Quotient (osetoid (X := X) K')) → Fin r :=
    fun xb => c (Φ (fun i => (xb i).out))
  obtain ⟨Ψb, ⟨blk, f, zb, hf, hcard, hΨb⟩, hcΨ⟩ := H₂ cb (ins_eq_all cb)
  choose e he using hf
  let Ψ : (Fin m → X) → (Fin n₀ → X) :=
    fun x i => (blk i).elim ((zb i).out) (fun j => g ^ e i • x j)
  have hΨ : IsBlk (LSub (X := X) K) m n₀ k₂ Ψ :=
    ⟨blk, fun i x => g ^ e i • x, fun i => (zb i).out,
      fun i => ⟨g ^ e i, K.pow_mem hg _, rfl⟩, hcard, fun x i => rfl⟩
  have hkey : ∀ x : Fin m → X,
      c (Φ (Ψ x)) = cb (Ψb (fun j => Quotient.mk (osetoid K') (x j))) := by
    intro x
    have hcls : ∀ i, Quotient.mk (osetoid K') (Ψ x i) =
        Ψb (fun j => Quotient.mk (osetoid K') (x j)) i := by
      intro i
      rw [hΨb]
      rcases hb : blk i with _ | j
      · simp [Ψ, hb]
      · simp only [Ψ, hb, Option.elim_some]
        rw [he i, hτe]
    exact Ins_congr hcΦ (Ψ x) _ (fun i => Or.inr (Quotient.exact
      ((hcls i).trans (Quotient.out_eq _).symm)))
  refine ⟨Φ ∘ Ψ, IsBlk_comp hLK hΦK hΨ, ?_⟩
  rintro x j a ⟨κ, hκ, ha⟩
  show c (Φ (Ψ x)) = c (Φ (Ψ (Function.update x j a)))
  rw [hkey, hkey]
  have hupd : (fun j' => Quotient.mk (osetoid K') (Function.update x j a j')) =
      Function.update (fun j' => Quotient.mk (osetoid K') (x j')) j
        (Quotient.mk (osetoid K') a) := by
    funext j'
    by_cases hj : j' = j
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [hupd]
  obtain ⟨e', he'⟩ := hcov κ hκ
  refine hcΨ _ j _ ⟨e', ?_⟩
  rw [hτe]
  exact Quotient.sound ⟨(κ * (g ^ e')⁻¹)⁻¹, K'.inv_mem he', by
    rw [ha, mul_inv_rev, inv_inv, mul_smul, inv_smul_smul]⟩

end RamseyDisambig.Dev.DB.PartD
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartD
open RamseyDisambig.Dev.DB Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
/-- A nontrivial subgroup of a finite solvable group has a normal subgroup of prime index,
together with an element generating the quotient. -/
theorem exists_prime_cyclic_quotient [Finite G] [Group.IsSolvable G] (K : Subgroup G) (hK : K ≠ ⊥) :
    ∃ (K' : Subgroup G) (g : G) (q : ℕ), K' ≤ K ∧ Nat.card K' < Nat.card K ∧
      (∀ κ ∈ K, ∀ a ∈ K', κ * a * κ⁻¹ ∈ K') ∧ g ∈ K ∧ (q + 1).Prime ∧ g ^ (q + 1) ∈ K' ∧
      (∀ κ ∈ K, ∃ e : ℕ, κ * (g ^ e)⁻¹ ∈ K') := by
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK
  have hC := Group.IsSolvable.commutator_lt_top_of_nontrivial K
  obtain ⟨M, hMc, hCM⟩ := (eq_top_or_exists_le_coatom (commutator K)).resolve_left hC.ne
  have hMn : M.Normal := ⟨fun m hm κ => by
    have h1 : κ * m * κ⁻¹ * m⁻¹ ∈ M := by
      have h0 := Subgroup.commutator_mem_commutator (G := K) (Subgroup.mem_top κ)
        (Subgroup.mem_top m)
      rw [commutatorElement_def] at h0
      exact hCM h0
    have := M.mul_mem h1 hm
    simpa [mul_assoc] using this⟩
  have hQ1 : Nat.card (K ⧸ M) ≠ 1 := fun h => hMc.1 (Subgroup.index_eq_one.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hQ1
  have := Fact.mk hp
  obtain ⟨abar, habar⟩ := exists_prime_orderOf_dvd_card' p hpd
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective abar
  have hgen : ∀ κ : K, ∃ e : ℕ, ((κ : K ⧸ M)) = (a : K ⧸ M) ^ e := by
    have htop : (Subgroup.zpowers (a : K ⧸ M)).comap (QuotientGroup.mk' M) = ⊤ := by
      have hle : M ≤ (Subgroup.zpowers (a : K ⧸ M)).comap (QuotientGroup.mk' M) := by
        intro x hx
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
        exact Subgroup.one_mem _
      rcases (hMc.le_iff).mp hle with h | h
      · exact h
      · exfalso
        have ha : a ∈ (Subgroup.zpowers (a : K ⧸ M)).comap (QuotientGroup.mk' M) := by
          rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]
          exact Subgroup.mem_zpowers _
        rw [h] at ha
        have : ((a : K ⧸ M)) = 1 := (QuotientGroup.eq_one_iff a).mpr ha
        rw [this, orderOf_one] at habar
        exact hp.one_lt.ne habar
    intro κ
    have hκ : κ ∈ (Subgroup.zpowers (a : K ⧸ M)).comap (QuotientGroup.mk' M) :=
      htop ▸ Subgroup.mem_top κ
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, ← mem_powers_iff_mem_zpowers] at hκ
    obtain ⟨e, he⟩ := hκ
    exact ⟨e, he.symm⟩
  have hp1 : p - 1 + 1 = p := by have := hp.two_le; omega
  refine ⟨M.map K.subtype, (a : G), p - 1, Subgroup.map_subtype_le M, ?_, ?_, a.2, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_eq_card_quotient_mul_card_subgroup M]
    have h1 : 0 < Nat.card M := Nat.card_pos
    have h2 : 0 < Nat.card (K ⧸ M) := Nat.card_pos
    have h3 : 2 ≤ Nat.card (K ⧸ M) := by omega
    nlinarith
  · intro κ hκ x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨⟨κ, hκ⟩ * m * ⟨κ, hκ⟩⁻¹, hMn.conj_mem m hm _, rfl⟩
  · rw [hp1]; exact hp
  · rw [hp1]
    refine Subgroup.mem_map.mpr ⟨a ^ p, ?_, by simp⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← habar, pow_orderOf_eq_one]
  · intro κ hκ
    obtain ⟨e, he⟩ := hgen ⟨κ, hκ⟩
    refine ⟨e, Subgroup.mem_map.mpr ⟨⟨κ, hκ⟩ * (a ^ e)⁻¹, ?_, by simp⟩⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, he, mul_inv_cancel]

end RamseyDisambig.Dev.DB.PartD
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartD
open RamseyDisambig.Dev.DB Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
theorem step_of_solvable [Finite G] [Group.IsSolvable G] [Finite X] [Nonempty X] (K : Subgroup G) :
    Step (LSub (X := X) K) (fun a b => a = b) (OSub K) := by
  induction hN : Nat.card K using Nat.strong_induction_on generalizing K with
  | _ N ih =>
  by_cases hK : K = ⊥
  · subst hK
    refine Step_mono (Step_refl (L := LSub (X := X) (⊥ : Subgroup G))
      ⟨1, Subgroup.one_mem _, by funext x; simp⟩ (fun a b => a = b))
      (fun f hf => hf) (fun a b h => h) ?_
    rintro a b ⟨κ, hκ, rfl⟩
    rw [Subgroup.mem_bot] at hκ
    subst hκ
    simp
  · obtain ⟨K', g, q, hle, hcard, hnorm, hg, hp, hgp, hcov⟩ :=
      RamseyDisambig.Dev.DB.PartD.exists_prime_cyclic_quotient K hK
    exact RamseyDisambig.Dev.DB.PartD.extension_step K' K hle hnorm g hg q hp hgp hcov
      (ih _ (hN ▸ hcard) K' rfl)

end RamseyDisambig.Dev.DB.PartD
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
alias step_of_solvable := RamseyDisambig.Dev.DB.PartD.step_of_solvable

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartD
open RamseyDisambig.Dev.DB Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
theorem denseBlock_of_step (hs : Step (LSub (X := X) (⊤ : Subgroup G)) (fun a b => a = b)
    (OSub (⊤ : Subgroup G))) : RamseyDisambig.Spherical.DenseBlockProperty G X := by
  intro r m hr hm η hη hη1
  obtain ⟨n, k, hn, hk, hd, H⟩ := hs r m hm η hη hη1
  refine ⟨n, k, hn, hk, hd, fun c => ?_⟩
  obtain ⟨φ, ⟨blk, f, z, hf, hcard, hφ⟩, hcφ⟩ := H c (ins_eq_all c)
  choose γ _ hγ using hf
  refine ⟨φ, ⟨fun j => Finset.univ.filter (fun ℓ => blk ℓ = some j), ?_, hcard, γ,
    fun s => z s.1, ?_, ?_⟩, ?_⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro ℓ h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hij (Option.some_injective _ (h1.symm.trans h2))
  · intro x j ℓ hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    rw [hφ, hℓ, hγ ℓ]
    rfl
  · intro x ℓ h
    rw [hφ]
    rcases hb : blk ℓ with _ | j
    · rfl
    · exact absurd (by simp [hb]) (h j)
  · intro x y hxy
    exact Ins_congr hcφ x y (fun j => Or.inr (by
      obtain ⟨g, hg⟩ := hxy j
      exact ⟨g, Subgroup.mem_top g, hg⟩))

end RamseyDisambig.Dev.DB.PartD
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
alias denseBlock_of_step := RamseyDisambig.Dev.DB.PartD.denseBlock_of_step

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB.PartD
open RamseyDisambig.Dev.DB Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
theorem denseBlock_of_isEmpty [IsEmpty X] : RamseyDisambig.Spherical.DenseBlockProperty G X := by
  intro r m hr hm η hη hη1
  refine ⟨m, 1, hm, le_rfl, by push_cast; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)],
    fun c => ?_⟩
  refine ⟨id, ⟨fun j => {j}, ?_, fun j => Finset.card_singleton j, fun _ => 1,
    fun s => absurd (Finset.mem_singleton_self s.1) (s.2 s.1), ?_, ?_⟩, ?_⟩
  · intro i j hij
    simpa using hij
  · intro x j ℓ hℓ
    rw [Finset.mem_singleton] at hℓ
    subst hℓ
    simp
  · intro x ℓ h
    exact absurd (Finset.mem_singleton_self ℓ) (h ℓ)
  · intro x y _
    congr 1
    funext j
    exact isEmptyElim (x j)

end RamseyDisambig.Dev.DB.PartD
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.DB
open Classical
universe u v
variable {G : Type u} [Group G] {X : Type v} [MulAction G X]
alias denseBlock_of_isEmpty := RamseyDisambig.Dev.DB.PartD.denseBlock_of_isEmpty

end RamseyDisambig.Dev.DB
end

section
set_option autoImplicit false
namespace RamseyDisambig.Spherical
open RamseyDisambig.Dev.DB in
theorem chk_theorem_11 (G X : Type*) [Group G] [Finite G] [Group.IsSolvable G]
    [Finite X] [MulAction G X] : DenseBlockProperty G X :=
  by
    rcases isEmpty_or_nonempty X with hX | hX
    · exact denseBlock_of_isEmpty
    · exact denseBlock_of_step (step_of_solvable ⊤)

end RamseyDisambig.Spherical
end

theorem solution : type_of% @RamseyDisambig.Spherical.chk_theorem_11 := @RamseyDisambig.Spherical.chk_theorem_11
