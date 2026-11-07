-- Prove2me | solution 1 for ThomsonKS.Char.replica_problem_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:44:45.592201+00:00
-- url     : https://prove2.me/submissions/4917880d-0680-486a-9076-504dba2eb36a

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

open ThomsonKS.Char

namespace KSReplica

lemma sum_ite_inj {α : Type*} [Fintype α] (f : α → ℕ) (hf : Function.Injective f)
    (s : α → ℝ) (q : ℕ) :
    (∑ p, if f p = q then s p else 0) = 0 ∨
      ∃ p, f p = q ∧ (∑ p, if f p = q then s p else 0) = s p := by
  by_cases h : ∃ p, f p = q
  · obtain ⟨p, hp⟩ := h
    right
    refine ⟨p, hp, ?_⟩
    rw [Finset.sum_eq_single p]
    · simp [hp]
    · intro b _ hb
      rw [if_neg]
      intro h'
      exact hb (hf (h'.trans hp.symm))
    · simp
  · left
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    intro h'
    exact h ⟨p, h'⟩

variable {P : Finset ℕ}

lemma zero_mem {S : Set (P → ℝ)} (hS : S ∈ DivProb P) : (0 : P → ℝ) ∈ S := by
  obtain ⟨x0, hx0, hx0p⟩ := hS.2.2.2.2.1
  exact hS.2.2.2.2.2 x0 hx0 0 le_rfl (fun i => (hx0p i).le)

/-- Compatibility of two embeddings `fj, fk : P → ℕ`. -/
def Compat (fj fk : P → ℕ) : Prop :=
  (∀ p p', fk p' = fj p → p' = p) ∨
    (∀ p1 p2 p1' p2', fk p1' = fj p1 → fk p2' = fj p2 → p1 = p2)

lemma compat_mem {S : Set (P → ℝ)} (hS : S ∈ DivProb P) (hle1 : ∀ x ∈ S, ∀ p, x p ≤ 1)
    (hatt : ∀ p, ∃ x ∈ S, x p = 1) {fj fk : P → ℕ} (hk : Function.Injective fk)
    (hc : Compat fj fk) {s : P → ℝ} (hs : s ∈ S) :
    (fun p => ∑ p', if fk p' = fj p then s p' else 0) ∈ S := by
  have hnn := hS.2.1
  have hcomp := hS.2.2.2.2.2
  have hA : (∀ p p', fk p' = fj p → p' = p) →
      (fun p => ∑ p', if fk p' = fj p then s p' else 0) ∈ S := by
    intro hA
    refine hcomp s hs _ (fun p => ?_) (fun p => ?_)
    · rcases sum_ite_inj fk hk s (fj p) with h | ⟨p', _, h⟩
      · simp only [Pi.zero_apply]; rw [h]
      · simp only [Pi.zero_apply]; rw [h]; exact hnn s hs p'
    · rcases sum_ite_inj fk hk s (fj p) with h | ⟨p', hp', h⟩
      · simp only; rw [h]; exact hnn s hs p
      · simp only; rw [h, hA p p' hp']
  rcases hc with hc | hc
  · exact hA hc
  · by_cases hcol : ∃ p p', fk p' = fj p
    · obtain ⟨ps, ps', hps⟩ := hcol
      obtain ⟨x, hx, hx1⟩ := hatt ps
      refine hcomp x hx _ (fun p => ?_) (fun p => ?_)
      · rcases sum_ite_inj fk hk s (fj p) with h | ⟨p', _, h⟩
        · simp only [Pi.zero_apply]; rw [h]
        · simp only [Pi.zero_apply]; rw [h]; exact hnn s hs p'
      · rcases sum_ite_inj fk hk s (fj p) with h | ⟨p', hp', h⟩
        · simp only; rw [h]; exact hnn x hx p
        · simp only; rw [h]
          have : p = ps := hc p ps p' ps' hp' hps
          subst this
          rw [hx1]; exact hle1 s hs p'
    · apply hA
      intro p p' h
      exact absurd ⟨p, p', h⟩ hcol

variable (Q : Finset ℕ) (J : Finset ℕ) (f : ℕ → P → ℕ)

/-- The embedded copy of `s` along `f k`. -/
def E (k : ℕ) (s : P → ℝ) : Q → ℝ := fun q => ∑ p, if f k p = q.1 then s p else 0

/-- The generators. -/
def Gen (S : Set (P → ℝ)) : Set (Q → ℝ) :=
  {g | ∃ k ∈ J, ∃ s ∈ S, g = E Q f k s} ∪
    {g | ∃ c : ℝ, (fun _ : P => c) ∈ S ∧ g = fun _ => c}

/-- The glued problem. -/
def Tset (S : Set (P → ℝ)) : Set (Q → ℝ) :=
  {y | 0 ≤ y ∧ ∃ z ∈ closure (convexHull ℝ (Gen Q J f S)), y ≤ z}

variable {Q J f}

section
variable {S : Set (P → ℝ)} (hS : S ∈ DivProb P) (hle1 : ∀ x ∈ S, ∀ p, x p ≤ 1)
  (hinj : ∀ k ∈ J, Function.Injective (f k)) (hmem : ∀ k ∈ J, ∀ p, f k p ∈ Q)
include hS hle1 hinj

lemma gen_icc : Gen Q J f S ⊆ Set.Icc 0 1 := by
  rintro g (⟨k, hk, s, hs, rfl⟩ | ⟨c, hc, rfl⟩)
  · refine ⟨fun q => ?_, fun q => ?_⟩
    · simp only [E, Pi.zero_apply]
      rcases sum_ite_inj (f k) (hinj k hk) s q.1 with h | ⟨p', _, h⟩
      · rw [h]
      · rw [h]; exact hS.2.1 s hs p'
    · simp only [E, Pi.one_apply]
      rcases sum_ite_inj (f k) (hinj k hk) s q.1 with h | ⟨p', _, h⟩
      · rw [h]; norm_num
      · rw [h]; exact hle1 s hs p'
  · obtain ⟨i, hi⟩ := hS.1
    exact ⟨fun q => hS.2.1 _ hc ⟨i, hi⟩, fun q => hle1 _ hc ⟨i, hi⟩⟩

omit hinj in
lemma gen_subset_T (hG : Gen Q J f S ⊆ Set.Icc 0 1) : Gen Q J f S ⊆ Tset Q J f S := by
  intro g hg
  exact ⟨(hG hg).1, g, subset_closure (subset_convexHull ℝ _ hg), le_rfl⟩

lemma T_mem (hQ : Q.Nonempty) : Tset Q J f S ∈ DivProb Q := by
  have hG := gen_icc (Q := Q) hS hle1 hinj
  set H := closure (convexHull ℝ (Gen Q J f S)) with hH
  have hHsub : H ⊆ Set.Icc 0 1 :=
    closure_minimal (convexHull_min hG (convex_Icc 0 1)) isClosed_Icc
  have hHc : IsCompact H := isCompact_Icc.of_isClosed_subset isClosed_closure hHsub
  have hHcvx : Convex ℝ H := (convex_convexHull ℝ _).closure
  refine ⟨hQ, fun x hx i => hx.1 i, ?_, ?_, ?_, ?_⟩
  · set K : Set ((Q → ℝ) × (Q → ℝ)) := {p | p.2 ∈ H ∧ 0 ≤ p.1 ∧ p.1 ≤ p.2} with hK
    have hKc : IsClosed K := hHc.isClosed.preimage continuous_snd |>.inter
      ((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_fst continuous_snd))
    have hKsub : K ⊆ Set.Icc (0 : Q → ℝ) 1 ×ˢ H := by
      rintro ⟨y, z⟩ ⟨hz, hy0, hyz⟩
      exact ⟨⟨hy0, hyz.trans (hHsub hz).2⟩, hz⟩
    have hKcpt : IsCompact K := (isCompact_Icc.prod hHc).of_isClosed_subset hKc hKsub
    have : Tset Q J f S = Prod.fst '' K := by
      ext y
      constructor
      · rintro ⟨hy, z, hz, hyz⟩
        exact ⟨(y, z), ⟨hz, hy, hyz⟩, rfl⟩
      · rintro ⟨⟨y, z⟩, ⟨hz, hy, hyz⟩, rfl⟩
        exact ⟨hy, z, hz, hyz⟩
    rw [this]
    exact hKcpt.image continuous_fst
  · rintro y ⟨hy, z, hz, hyz⟩ y' ⟨hy', z', hz', hyz'⟩ a b ha hb hab
    refine ⟨?_, a • z + b • z', hHcvx hz hz' ha hb hab, ?_⟩
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have := hy i; have := hy' i
      simp only [Pi.zero_apply] at *
      positivity
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left (hyz i) ha
      have h2 := mul_le_mul_of_nonneg_left (hyz' i) hb
      linarith
  · obtain ⟨x0, hx0, hx0p⟩ := hS.2.2.2.2.1
    haveI : Nonempty P := by obtain ⟨i, hi⟩ := hS.1; exact ⟨⟨i, hi⟩⟩
    obtain ⟨i₀, hi₀⟩ := Finite.exists_min x0
    have hcS : (fun _ : P => x0 i₀) ∈ S :=
      hS.2.2.2.2.2 x0 hx0 _ (fun i => (hx0p i₀).le) (fun i => hi₀ i)
    refine ⟨fun _ => x0 i₀, gen_subset_T hS hle1 hG (Or.inr ⟨x0 i₀, hcS, rfl⟩),
      fun _ => hx0p i₀⟩
  · rintro x ⟨hx, z, hz, hxz⟩ y hy hyx
    exact ⟨hy, z, hz, hyx.trans hxz⟩

include hmem in
lemma slice_eq {P' : Finset ℕ} (h : P' ⊆ Q) (σ : P ≃ P') {j : ℕ} (hj : j ∈ J)
    (hσ : ∀ p, ((σ p : P') : ℕ) = f j p) (hatt : ∀ p, ∃ x ∈ S, x p = 1)
    (hcompat : ∀ k ∈ J, Compat (f j) (f k)) :
    {x | zeroExt h x ∈ Tset Q J f S} = relabel σ S := by
  have hG := gen_icc (Q := Q) hS hle1 hinj
  ext x
  constructor
  · rintro ⟨hx0, z, hz, hxz⟩
    set π : (Q → ℝ) → (P → ℝ) := fun z p => z ⟨f j p, hmem j hj p⟩ with hπ
    have hπlin : IsLinearMap ℝ π := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    have hπc : Continuous π := continuous_pi fun p => continuous_apply _
    have hGS : Gen Q J f S ⊆ π ⁻¹' S := by
      rintro g (⟨k, hk, s, hs, rfl⟩ | ⟨c, hc, rfl⟩)
      · exact compat_mem hS hle1 hatt (hinj k hk) (hcompat k hk) hs
      · exact hc
    have hHS : closure (convexHull ℝ (Gen Q J f S)) ⊆ π ⁻¹' S :=
      closure_minimal (convexHull_min hGS (hS.2.2.2.1.is_linear_preimage hπlin))
        (hS.2.2.1.isClosed.preimage hπc)
    have hzS : π z ∈ S := hHS hz
    refine ⟨fun p => x (σ p), ?_, fun p => rfl⟩
    refine hS.2.2.2.2.2 _ hzS _ (fun p => ?_) (fun p => ?_)
    · have := hx0 ⟨σ p, h (σ p).2⟩
      simpa [zeroExt] using this
    · have := hxz ⟨σ p, h (σ p).2⟩
      simp only [zeroExt, Subtype.coe_eta, dite_true, (σ p).2] at this
      simp only [hπ]
      have e : (⟨f j p, hmem j hj p⟩ : Q) = ⟨σ p, h (σ p).2⟩ := Subtype.ext (hσ p).symm
      rw [e]
      exact this
  · rintro ⟨s, hs, hxs⟩
    have heq : zeroExt h x = E Q f j s := by
      funext q
      simp only [zeroExt, E]
      split_ifs with hq
      · set p0 := σ.symm ⟨q.1, hq⟩
        have hp0 : f j p0 = q.1 := by
          rw [← hσ p0]; simp [p0]
        rw [Finset.sum_eq_single p0]
        · rw [if_pos hp0, ← hxs p0]; simp [p0]
        · intro b _ hb
          rw [if_neg]
          intro h'
          exact hb (hinj j hj (h'.trans hp0.symm))
        · simp
      · symm
        apply Finset.sum_eq_zero
        intro p _
        rw [if_neg]
        intro h'
        apply hq
        rw [← h', ← hσ p]
        exact (σ p).2
    show zeroExt h x ∈ Tset Q J f S
    rw [heq]
    exact gen_subset_T hS hle1 hG (Or.inl ⟨j, hj, s, hs, rfl⟩)

end

namespace Inst

variable (P : Finset ℕ) (i₀ : ℕ)

def M : ℕ := P.sup id + 1

def lev (j : ℕ) : ℕ :=
  if j < M P then (if j = i₀ then 2 else 0) else if j < 2 * M P then 1 else 2

def cof (j : ℕ) : ℕ := (lev P i₀ j + 1) % 3

def fe (j : ℕ) (p : P) : ℕ := if (p : ℕ) = i₀ then j else p + cof P i₀ j * M P

def Qs : Finset ℕ :=
  P ∪ (P.erase i₀).image (· + M P) ∪ (P.erase i₀).image (· + 2 * M P)

variable {P i₀}

lemma lt_M {p : ℕ} (hp : p ∈ P) : p < M P :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hp)

lemma lev_lt (j : ℕ) : lev P i₀ j < 3 := by
  unfold lev; split_ifs <;> omega

lemma cof_lt (j : ℕ) : cof P i₀ j < 3 := Nat.mod_lt _ (by norm_num)

lemma lev_shift {p : ℕ} (hp : p ∈ P) (hpi : p ≠ i₀) {c : ℕ} (hc : c < 3) :
    lev P i₀ (p + c * M P) = c := by
  have := lt_M hp
  interval_cases c <;> simp only [lev] <;> split_ifs <;> omega

lemma ne_shift {p : ℕ} (hp : p ∈ P) (hpi : p ≠ i₀) (j : ℕ) : j ≠ p + cof P i₀ j * M P := by
  intro h
  have h1 := lev_shift hp hpi (cof_lt (P := P) (i₀ := i₀) j)
  rw [← h] at h1
  have h2 := lev_lt (P := P) (i₀ := i₀) j
  simp only [cof] at h1
  omega

lemma fe_inj (j : ℕ) : Function.Injective (fe P i₀ j) := by
  intro p1 p2 h
  simp only [fe] at h
  split_ifs at h with h1 h2 h2
  · exact Subtype.ext (h1.trans h2.symm)
  · exact absurd h (ne_shift p2.2 h2 j)
  · exact absurd h.symm (ne_shift p1.2 h1 j)
  · exact Subtype.ext (by omega)

lemma mem_Qs {j : ℕ} : j ∈ Qs P i₀ ↔ j ∈ P ∨ (∃ r ∈ P.erase i₀, r + M P = j) ∨
    (∃ r ∈ P.erase i₀, r + 2 * M P = j) := by
  simp [Qs, or_assoc]

lemma fe_mem {j : ℕ} (hj : j ∈ Qs P i₀) (p : P) : fe P i₀ j p ∈ Qs P i₀ := by
  simp only [fe]
  split_ifs with h
  · exact hj
  · rw [mem_Qs]
    have hc := cof_lt (P := P) (i₀ := i₀) j
    have hr : (p : ℕ) ∈ P.erase i₀ := Finset.mem_erase.mpr ⟨h, p.2⟩
    interval_cases hcj : cof P i₀ j
    · left; simpa using p.2
    · right; left; exact ⟨p, hr, by ring⟩
    · right; right; exact ⟨p, hr, rfl⟩

lemma lev_i0 (hi₀ : i₀ ∈ P) : lev P i₀ i₀ = 2 := by
  have := lt_M hi₀
  simp [lev, this]

lemma fe_i0 (hi₀ : i₀ ∈ P) (p : P) : fe P i₀ i₀ p = p := by
  simp only [fe]
  split_ifs with h
  · exact h.symm
  · simp [cof, lev_i0 hi₀]

lemma collision {j k : ℕ} {p p' : P} (h : fe P i₀ k p' = fe P i₀ j p)
    (hne : cof P i₀ j ≠ cof P i₀ k) :
    ((p : ℕ) = i₀ ∧ lev P i₀ j = cof P i₀ k) ∨
      ((p : ℕ) ≠ i₀ ∧ k = p + cof P i₀ j * M P ∧ lev P i₀ k = cof P i₀ j) := by
  simp only [fe] at h
  have hp := lt_M p.2
  have hp' := lt_M p'.2
  have hcj := cof_lt (P := P) (i₀ := i₀) j
  have hck := cof_lt (P := P) (i₀ := i₀) k
  split_ifs at h with h1 h2 h2
  · exfalso; apply hne; rw [h]
  · right; refine ⟨h2, h, ?_⟩
    rw [h]; exact lev_shift p.2 h2 hcj
  · left; refine ⟨h2, ?_⟩
    rw [← h]; exact lev_shift p'.2 h1 hck
  · exfalso
    interval_cases hcj' : cof P i₀ j <;> interval_cases hck' : cof P i₀ k <;> omega

lemma compat (j k : ℕ) : Compat (fe P i₀ j) (fe P i₀ k) := by
  by_cases hc : cof P i₀ j = cof P i₀ k
  · left
    intro p p' h
    simp only [fe] at h
    split_ifs at h with h1 h2 h2
    · exact Subtype.ext (h1.trans h2.symm)
    · exact absurd h (by rw [hc]; exact ne_shift p.2 h2 k)
    · exact absurd h.symm (by rw [← hc]; exact ne_shift p'.2 h1 j)
    · exact Subtype.ext (by rw [hc] at h; omega)
  · right
    intro p1 p2 p1' p2' h1 h2
    have hlj := lev_lt (P := P) (i₀ := i₀) j
    have hlk := lev_lt (P := P) (i₀ := i₀) k
    rcases collision h1 hc with ⟨a1, b1⟩ | ⟨a1, b1, c1⟩ <;>
      rcases collision h2 hc with ⟨a2, b2⟩ | ⟨a2, b2, c2⟩
    · exact Subtype.ext (a1.trans a2.symm)
    · exfalso; simp only [cof] at *; omega
    · exfalso; simp only [cof] at *; omega
    · exact Subtype.ext (by omega)

end Inst

end KSReplica

open KSReplica

theorem solution (P : Finset ℕ) (i₀ : ℕ) (hi₀ : i₀ ∈ P) (S : Set (P → ℝ))
    (hS : S ∈ DivProb P) (ha : idealPt S = fun _ => 1) (a : ℝ) (haS : (fun _ => a) ∈ S) :
    ∃ Q : Finset ℕ, ∃ hPQ : P ⊆ Q, Q.card = 3 * P.card - 2 ∧
      ∃ T ∈ DivProb Q, {x | zeroExt hPQ x ∈ T} = S ∧ (fun _ => a) ∈ T ∧
        ∀ j ∈ Q, ∃ Pj : Finset ℕ, ∃ hPj : Pj ⊆ Q, ∃ hj : j ∈ Pj,
          ∃ σ : P ≃ Pj, σ ⟨i₀, hi₀⟩ = ⟨j, hj⟩ ∧
            {x | zeroExt hPj x ∈ T} = relabel σ S := by
  open Inst in
  have hbdd : ∀ p : P, BddAbove ((fun x : P → ℝ => x p) '' S) := fun p =>
    (hS.2.2.1.image (continuous_apply p)).bddAbove
  have hle1 : ∀ x ∈ S, ∀ p, x p ≤ 1 := by
    intro x hx p
    have := le_csSup (hbdd p) ⟨x, hx, rfl⟩
    have e : idealPt S p = 1 := by rw [ha]
    exact this.trans e.le
  have hatt : ∀ p, ∃ x ∈ S, x p = 1 := by
    intro p
    obtain ⟨x0, hx0, -⟩ := hS.2.2.2.2.1
    obtain ⟨x, hx, h⟩ := (hS.2.2.1.image (continuous_apply p)).sSup_mem ⟨_, x0, hx0, rfl⟩
    refine ⟨x, hx, ?_⟩
    have e : idealPt S p = 1 := by rw [ha]
    exact h.trans e
  set Q := Inst.Qs P i₀ with hQ
  set f := Inst.fe P i₀ with hf
  have hinj : ∀ k ∈ Q, Function.Injective (f k) := fun k _ => Inst.fe_inj k
  have hmem : ∀ k ∈ Q, ∀ p, f k p ∈ Q := fun k hk p => Inst.fe_mem hk p
  have hPQ : P ⊆ Q := fun p hp => Inst.mem_Qs.mpr (Or.inl hp)
  have hQne : Q.Nonempty := ⟨i₀, hPQ hi₀⟩
  have hi₀Q : i₀ ∈ Q := hPQ hi₀
  refine ⟨Q, hPQ, ?_, Tset Q Q f S, T_mem hS hle1 hinj hQne, ?_, ?_, ?_⟩
  · -- cardinality
    have hM : ∀ p ∈ P, p < Inst.M P := fun p hp => Inst.lt_M hp
    have hd1 : Disjoint P ((P.erase i₀).image (· + Inst.M P)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hx'
      have := hM _ hx; omega
    have hd2 : Disjoint (P ∪ (P.erase i₀).image (· + Inst.M P))
        ((P.erase i₀).image (· + 2 * Inst.M P)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx'
      have hr' := hM r (Finset.mem_of_mem_erase hr)
      rcases Finset.mem_union.mp hx with h | h
      · have := hM _ h; omega
      · obtain ⟨r', hr'', e⟩ := Finset.mem_image.mp h
        have := hM r' (Finset.mem_of_mem_erase hr''); omega
    have hc1 : ((P.erase i₀).image (· + Inst.M P)).card = P.card - 1 := by
      rw [Finset.card_image_of_injective _ (add_left_injective _), Finset.card_erase_of_mem hi₀]
    have hc2 : ((P.erase i₀).image (· + 2 * Inst.M P)).card = P.card - 1 := by
      rw [Finset.card_image_of_injective _ (add_left_injective _), Finset.card_erase_of_mem hi₀]
    have hpos : 0 < P.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
    rw [hQ, Inst.Qs, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hc1, hc2]
    omega
  · -- slice on P
    have := slice_eq hS hle1 hinj hmem hPQ (Equiv.refl P) hi₀Q
      (fun p => (Inst.fe_i0 hi₀ p).symm) hatt (fun k _ => Inst.compat i₀ k)
    rw [this]
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : x = y := funext fun p => hxy p
      rw [this]; exact hy
    · intro hx
      exact ⟨x, hx, fun p => rfl⟩
  · exact gen_subset_T hS hle1 (gen_icc hS hle1 hinj) (Or.inr ⟨a, haS, rfl⟩)
  · intro j hj
    set Pj : Finset ℕ := Finset.univ.image (f j) with hPj_def
    have hPj : Pj ⊆ Q := by
      intro q hq
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hq
      exact hmem j hj p
    have hjP : j ∈ Pj := Finset.mem_image.mpr ⟨⟨i₀, hi₀⟩, Finset.mem_univ _, by simp [hf, Inst.fe]⟩
    set g : P → Pj := fun p => ⟨f j p, Finset.mem_image_of_mem _ (Finset.mem_univ p)⟩ with hg
    have hgb : Function.Bijective g := by
      refine ⟨fun p1 p2 h => hinj j hj (congrArg Subtype.val h), ?_⟩
      rintro ⟨q, hq⟩
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨p, rfl⟩
    refine ⟨Pj, hPj, hjP, Equiv.ofBijective g hgb, ?_, ?_⟩
    · apply Subtype.ext
      simp [hg, hf, Inst.fe]
    · exact slice_eq hS hle1 hinj hmem hPj (Equiv.ofBijective g hgb) hj (fun p => rfl) hatt
        (fun k _ => Inst.compat j k)
