-- Prove2me | solution 1 for PeriodicCostas.rubio_torres_conjecture_1
-- status  : ACCEPTED   (disprove)
-- author  : @shivm
-- created : 2026-10-04T17:45:13.191993+00:00
-- url     : https://prove2.me/submissions/15ec609d-ebaa-4295-a022-fbcc585691fb

import Definitions.Def_PeriodicCostasArray

namespace PeriodicCostas.Disproof

open PeriodicCostas

/-- Side lengths `(2, 3)`. -/
def A : Fin 2 → ℕ := ![2, 3]

/-- The bijection `[2] × [3] → [2] × [3]`. -/
def phi (x : Fin 2 → ℤ) : Fin 2 → ℤ :=
  if x 0 = 1 ∧ x 1 = 1 then ![1, 1]
  else if x 0 = 1 ∧ x 1 = 2 then ![1, 2]
  else if x 0 = 1 ∧ x 1 = 3 then ![2, 1]
  else if x 0 = 2 ∧ x 1 = 1 then ![1, 3]
  else if x 0 = 2 ∧ x 1 = 2 then ![2, 3]
  else ![2, 2]

instance decBox (n : Fin 2 → ℕ) : DecidablePred (· ∈ box n) := fun x =>
  inferInstanceAs (Decidable (∀ i, 1 ≤ x i ∧ x i ≤ (n i : ℤ)))

instance decDots : DecidablePred (· ∈ dots A A phi) := fun p =>
  inferInstanceAs (Decidable (p.1 ∈ box A ∧ p.2 ∈ box A ∧ phi p.1 = p.2))

/-- Explicit enumeration of `[2] × [3]`. -/
def boxL : List (Fin 2 → ℤ) := [![1, 1], ![1, 2], ![1, 3], ![2, 1], ![2, 2], ![2, 3]]

/-- Explicit enumeration of residues `{0,1} × {0,1,2}`. -/
def resL : List (Fin 2 → ℤ) := [![0, 0], ![0, 1], ![0, 2], ![1, 0], ![1, 1], ![1, 2]]

/-- The offsets `u ∈ Λ` such that `t + u` is a dot, for `t ≡ ρ`. -/
def Lr (ρ : (Fin 2 → ℤ) × (Fin 2 → ℤ)) : List ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (boxL ×ˢ boxL).filter
    (fun u => decide ((reduce A (ρ.1 + u.1), reduce A (ρ.2 + u.2)) ∈ dots A A phi))

def diffs {V : Type*} [AddCommGroup V] [DecidableEq V] (L : List V) : List V :=
  ((L ×ˢ L).filter (fun q => decide (q.1 ≠ q.2))).map (fun q => q.2 - q.1)

lemma nrd_list {V : Type*} [AddCommGroup V] [DecidableEq V] (L : List V)
    (h : (diffs L).Nodup) : ∀ α ∈ L, ∀ ω ∈ L, ∀ α' ∈ L, ∀ ω' ∈ L,
      α ≠ ω → α' ≠ ω' → ω - α = ω' - α' → α = α' ∧ ω = ω' := by
  intro α hα ω hω α' hα' ω' hω' h1 h2 h3
  have := List.inj_on_of_nodup_map h (x := (α, ω)) (y := (α', ω'))
    (by simp [List.mem_filter, List.mem_product, hα, hω, h1])
    (by simp [List.mem_filter, List.mem_product, hα', hω', h2]) h3
  simpa using this

lemma eta2 (x : Fin 2 → ℤ) : x = ![x 0, x 1] := by
  ext i; fin_cases i <;> rfl

lemma mem_boxL {x : Fin 2 → ℤ} : x ∈ box A ↔ x ∈ boxL := by
  constructor
  · intro hx
    have h0 := hx 0
    have h1 := hx 1
    simp [A] at h0 h1
    have e0 : x 0 = 1 ∨ x 0 = 2 := by omega
    have e1 : x 1 = 1 ∨ x 1 = 2 ∨ x 1 = 3 := by omega
    rw [eta2 x]
    rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1 | e1 <;> rw [e0, e1] <;> decide
  · intro hx
    simp only [boxL, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

lemma mem_resL {x : Fin 2 → ℤ} (h0 : 0 ≤ x 0 ∧ x 0 < 2) (h1 : 0 ≤ x 1 ∧ x 1 < 3) :
    x ∈ resL := by
  have e0 : x 0 = 0 ∨ x 0 = 1 := by omega
  have e1 : x 1 = 0 ∨ x 1 = 1 ∨ x 1 = 2 := by omega
  rw [eta2 x]
  rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1 | e1 <;> rw [e0, e1] <;> decide

lemma reduce_shift (n : Fin 2 → ℕ) (t p : Fin 2 → ℤ) :
    reduce n ((fun i => t i % (n i : ℤ)) + (p - t)) = reduce n p := by
  funext i
  simp only [reduce, Pi.add_apply, Pi.sub_apply]
  have h := Int.emod_add_ediv_mul (t i) (n i : ℤ)
  have : p i - 1 = (t i % (n i : ℤ) + (p i - t i) - 1) + (t i / (n i : ℤ)) * (n i : ℤ) := by
    linarith
  rw [this, Int.add_mul_emod_self_right]

lemma reduce_box (x : Fin 2 → ℤ) (hx : x ∈ box A) : reduce A x = x := by
  funext i
  have := hx i
  simp only [reduce]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  ring

/-- The finite check: every residue class of offsets gives a window with distinct differences. -/
lemma finite_check : ∀ r1 ∈ resL, ∀ r2 ∈ resL, (diffs (Lr (r1, r2))).Nodup := by
  decide +kernel

lemma bij : Set.BijOn phi (box A) (box A) := by
  have hm : ∀ x ∈ boxL, phi x ∈ boxL := by decide +kernel
  have hi : ∀ x ∈ boxL, ∀ y ∈ boxL, phi x = phi y → x = y := by decide +kernel
  have hs : ∀ y ∈ boxL, ∃ x ∈ boxL, phi x = y := by decide +kernel
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · exact mem_boxL.2 (hm x (mem_boxL.1 hx))
  · exact hi x (mem_boxL.1 hx) y (mem_boxL.1 hy) hxy
  · obtain ⟨x, hx, rfl⟩ := hs y (mem_boxL.1 hy)
    exact ⟨x, mem_boxL.2 hx, rfl⟩

lemma window_nrd (t : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    NoRepeatedDifferences (periodicDots A A phi ∩ window A A t) := by
  set ρ : (Fin 2 → ℤ) × (Fin 2 → ℤ) :=
    ((fun i => t.1 i % (A i : ℤ)), (fun i => t.2 i % (A i : ℤ))) with hρ
  have hres : ∀ s : Fin 2 → ℤ, (fun i => s i % (A i : ℤ)) ∈ resL := by
    intro s
    apply mem_resL
    · show 0 ≤ s 0 % 2 ∧ s 0 % 2 < 2
      omega
    · show 0 ≤ s 1 % 3 ∧ s 1 % 3 < 3
      omega
  have hmem : ∀ p ∈ periodicDots A A phi ∩ window A A t, p - t ∈ Lr ρ := by
    rintro p ⟨hp, hw⟩
    simp only [Lr, List.mem_filter, decide_eq_true_eq, Prod.fst_sub, Prod.snd_sub]
    refine ⟨List.mem_product.2 ⟨mem_boxL.1 hw.1, mem_boxL.1 hw.2⟩, ?_⟩
    rw [hρ]
    simp only
    rw [reduce_shift, reduce_shift]
    exact hp
  have hc := finite_check ρ.1 (hres _) ρ.2 (hres _)
  intro α hα ω hω α' hα' ω' hω' h1 h2 h3
  have := nrd_list _ hc (α - t) (hmem α hα) (ω - t) (hmem ω hω) (α' - t) (hmem α' hα')
    (ω' - t) (hmem ω' hω') (by simpa using h1) (by simpa using h2) (by simpa using h3)
  simpa using this

lemma periodic : IsPeriodicCostas A A phi := by
  refine ⟨⟨⟨by norm_num, by norm_num, ?_, ?_, bij⟩, ?_⟩, window_nrd⟩
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · have hsub : dots A A phi ⊆ periodicDots A A phi ∩ window A A 0 := by
      rintro p ⟨h1, h2, h3⟩
      refine ⟨?_, ?_⟩
      · show (reduce A p.1, reduce A p.2) ∈ dots A A phi
        rw [reduce_box _ h1, reduce_box _ h2]
        exact ⟨h1, h2, h3⟩
      · show p.1 - 0 ∈ box A ∧ p.2 - 0 ∈ box A
        simpa using And.intro h1 h2
    intro α hα ω hω α' hα' ω' hω'
    exact window_nrd 0 α (hsub hα) ω (hsub hω) α' (hsub hα') ω' (hsub hω')

end PeriodicCostas.Disproof

open PeriodicCostas in
theorem solution : ¬ (∀ {k l : ℕ} (hl : 1 ≤ l) (hlk : l ≤ k)
    (a : Fin k → ℕ) (b : Fin l → ℕ) (φ : (Fin k → ℤ) → (Fin l → ℤ))
    (hA : IsPeriodicCostas a b φ), ∏ i, a i = 2 ^ k) := by
  intro h
  have := h (k := 2) (l := 2) (by norm_num) le_rfl PeriodicCostas.Disproof.A
    PeriodicCostas.Disproof.A PeriodicCostas.Disproof.phi PeriodicCostas.Disproof.periodic
  simp [PeriodicCostas.Disproof.A, Fin.prod_univ_two] at this

#print axioms solution
