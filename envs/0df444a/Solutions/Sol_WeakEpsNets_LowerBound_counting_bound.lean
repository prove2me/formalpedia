-- Prove2me | solution 1 for WeakEpsNets.LowerBound.counting_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:10:18.365484+00:00
-- url     : https://prove2.me/submissions/be7520a9-2edd-4132-8a51-a212d7cd1c2a

import Mathlib
import Definitions.Def_WeakEpsNets_LowerBound_Parameters
import Definitions.Def_WeakEpsNets_LowerBound_Construction
import Definitions.Def_WeakEpsNets_LowerBound_Nets
import Theorems.Thm_WeakEpsNets_LowerBound_lemma_2

section
set_option autoImplicit false

namespace WeakEpsNets.Dev

open WeakEpsNets.LowerBound

end WeakEpsNets.Dev
end

section
set_option autoImplicit false

namespace WeakEpsNets.Dev.CBGeo

open WeakEpsNets.LowerBound

theorem var0 {α : Type*} (ι : Finset α) (w a : α → ℝ) (c : ℝ) (hw : ∀ i ∈ ι, 0 ≤ w i)
    (h1 : ∑ i ∈ ι, w i = 1) (h2 : ∑ i ∈ ι, w i * a i = c)
    (h3 : ∑ i ∈ ι, w i * a i ^ 2 = c ^ 2) :
    ∀ i ∈ ι, 0 < w i → a i = c := by
  have hsum : ∑ i ∈ ι, w i * (a i - c) ^ 2 = 0 := by
    have : ∑ i ∈ ι, w i * (a i - c) ^ 2 =
        ∑ i ∈ ι, w i * a i ^ 2 - 2 * c * ∑ i ∈ ι, w i * a i + c ^ 2 * ∑ i ∈ ι, w i := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intros; ring
    rw [this, h1, h2, h3]; ring
  intro i hi hwi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j hj => mul_nonneg (hw j hj) (sq_nonneg _))).1 hsum i hi
  have h := (mul_eq_zero.1 h0).resolve_left hwi.ne'
  have := (pow_eq_zero_iff (two_ne_zero)).1 h
  linarith

theorem mem_block_iff (s q : ℕ) (h : HyperplaneIndex s q) (p : Fin (s + 1) → ℝ) :
    p ∈ block s q h ↔ p ∈ shiftedGrid s q ∧ p ∈ hyperplane s q h := by
  classical
  simp [block, Finset.mem_filter]

theorem grid_nonneg (s q : ℕ) (p : Fin (s + 1) → ℝ) (hp : p ∈ shiftedGrid s q)
    (i : Fin (s + 1)) (hi : i.val < s) : 0 ≤ p i := by
  classical
  simp only [shiftedGrid, Finset.mem_image, Finset.mem_univ, true_and] at hp
  obtain ⟨t, rfl⟩ := hp
  simp only [hi, dif_pos]
  positivity

theorem tau_pos (q : ℕ) (hq : 2 ≤ q) : 0 < tau q := by
  unfold tau
  have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  positivity

theorem convex_pos (s q : ℕ) (hs : 1 ≤ s) (hq : 2 ≤ q) (h : HyperplaneIndex s q)
    {α : Type*} (ι : Finset α) (f : α → Fin (s + 1) → ℝ) (w : α → ℝ) (p : Fin (s + 1) → ℝ)
    (hp : p ∈ block s q h) (hf : ∀ i ∈ ι, f i ∈ block s q h) (hw : ∀ i ∈ ι, 0 ≤ w i)
    (h1 : ∑ i ∈ ι, w i = 1) (h2 : ∑ i ∈ ι, w i • phi s (f i) = phi s p) :
    ∀ i ∈ ι, 0 < w i → f i = p := by
  have hlin : ∀ c : Fin (s + 1), c.val < s - 1 → ∑ i ∈ ι, w i * f i c = p c := by
    intro c hc
    have := congrFun h2 (Sum.inl ⟨c.val, hc⟩)
    simpa [phi, Finset.sum_apply] using this
  have hquad : ∀ a b : Fin (s + 1), a ≤ b →
      ∑ i ∈ ι, w i * (f i a * f i b) = p a * p b := by
    intro a b hab
    have := congrFun h2 (Sum.inr ⟨(a, b), hab⟩)
    simpa [phi, Finset.sum_apply] using this
  -- step (a)
  have stepa : ∀ c : Fin (s + 1), c.val < s - 1 → ∀ i ∈ ι, 0 < w i → f i c = p c := by
    intro c hc
    apply var0 ι w (fun i => f i c) (p c) hw h1 (hlin c hc)
    have := hquad c c le_rfl
    simpa [sq] using this
  -- the free coordinate
  have hs' : s - 1 < s := by omega
  let jl' : Fin s := ⟨s - 1, hs'⟩
  let jl : Fin (s + 1) := ⟨s - 1, by omega⟩
  have hcs : jl'.castSucc = jl := Fin.ext rfl
  let a : Fin s → ℝ := fun j => (((h.1 j).val + 1 : ℕ) : ℝ)
  let c0 : ℝ := ((h.2.val + 1 : ℕ) : ℝ) + tau q
  have hsplit : ∀ p' ∈ hyperplane s q h,
      p' (Fin.last s) = a jl' * p' jl + (∑ j ∈ Finset.univ.erase jl', a j * p' j.castSucc) + c0 := by
    intro p' hp'
    have e : p' (Fin.last s) = (∑ i : Fin s, a i * p' i.castSucc) + c0 := by
      have := hp'
      simp only [hyperplane, Set.mem_ofPred_eq] at this
      rw [this]; ring
    rw [e, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ jl'), hcs]
  have hA : 0 < a jl' := by
    show (0 : ℝ) < (((h.1 jl').val + 1 : ℕ) : ℝ)
    positivity
  set A := a jl' with hAdef
  set E : ℝ := ∑ j ∈ Finset.univ.erase jl', a j * p j.castSucc with hE
  have hc0 : 0 < c0 := by
    have := tau_pos q hq
    have : (0 : ℝ) ≤ ((h.2.val + 1 : ℕ) : ℝ) := by positivity
    show 0 < ((h.2.val + 1 : ℕ) : ℝ) + tau q
    linarith
  have hE0 : 0 ≤ E := by
    apply Finset.sum_nonneg
    intro j hj
    have hpg := ((mem_block_iff s q h p).1 hp).1
    have := grid_nonneg s q p hpg j.castSucc (by simp)
    have : 0 ≤ a j := by positivity
    positivity
  set K : ℝ := E + c0 with hK
  have hKpos : 0 < K := by linarith
  have hP : p (Fin.last s) = A * p jl + K := by
    have := hsplit p ((mem_block_iff s q h p).1 hp).2
    rw [this]; ring
  -- for w_i > 0, f i (last) = A ξ_i + K
  have hlast : ∀ i ∈ ι, 0 < w i → f i (Fin.last s) = A * f i jl + K := by
    intro i hi hwi
    have := hsplit (f i) ((mem_block_iff s q h (f i)).1 (hf i hi)).2
    rw [this]
    have hEi : ∑ j ∈ Finset.univ.erase jl', a j * f i j.castSucc = E := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≠ jl' := Finset.ne_of_mem_erase hj
      have hjv : j.val < s - 1 := by
        have : j.val ≠ s - 1 := fun hh => hj' (Fin.ext hh)
        have := j.isLt
        omega
      rw [stepa j.castSucc (by simpa using hjv) i hi hwi]
    rw [hEi, hK]; ring
  have hq1 := hquad jl jl le_rfl
  have hqL := hquad (Fin.last s) (Fin.last s) le_rfl
  have hm1 : ∑ i ∈ ι, w i * f i jl = p jl := by
    have hexp : ∑ i ∈ ι, w i * (f i (Fin.last s) * f i (Fin.last s)) =
        A ^ 2 * ∑ i ∈ ι, w i * f i jl * f i jl + 2 * A * K * ∑ i ∈ ι, w i * f i jl
          + K ^ 2 * ∑ i ∈ ι, w i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hwi : 0 < w i
      · rw [hlast i hi hwi]; ring
      · have : w i = 0 := le_antisymm (not_lt.1 hwi) (hw i hi)
        rw [this]; ring
    have hq1' : ∑ i ∈ ι, w i * f i jl * f i jl = p jl * p jl := by
      rw [← hq1]; apply Finset.sum_congr rfl; intros; ring
    rw [hexp, hq1', h1, hP] at hqL
    have : 2 * A * K * (∑ i ∈ ι, w i * f i jl - p jl) = 0 := by nlinarith
    have hne : 2 * A * K ≠ 0 := by positivity
    have := (mul_eq_zero.1 this).resolve_left hne
    linarith
  have stepb : ∀ i ∈ ι, 0 < w i → f i jl = p jl := by
    apply var0 ι w (fun i => f i jl) (p jl) hw h1 hm1
    simpa [sq] using hq1
  intro i hi hwi
  funext c
  by_cases hc : c.val < s - 1
  · exact stepa c hc i hi hwi
  · by_cases hc2 : c.val = s - 1
    · have : c = jl := Fin.ext hc2
      rw [this]; exact stepb i hi hwi
    · have : c = Fin.last s := Fin.ext (by have := c.isLt; simp; omega)
      rw [this, hlast i hi hwi, hP, stepb i hi hwi]

theorem phi_injOn (s q : ℕ) (hs : 1 ≤ s) (hq : 2 ≤ q) (h : HyperplaneIndex s q) :
    Set.InjOn (phi s) (block s q h : Set (Fin (s + 1) → ℝ)) := by
  classical
  intro p hp p' hp' he
  have := convex_pos s q hs hq h ({p'} : Finset (Fin (s + 1) → ℝ)) id (fun _ => (1 : ℝ)) p hp
    (by simpa using hp') (by simp) (by simp)
    (by simp [he]) p' (by simp) (by simp)
  exact this.symm

/-- Convex position: a lifted block point in the hull of lifted block points is one of them. -/
theorem mem_of_mem_hull (s q : ℕ) (hs : 1 ≤ s) (hq : 2 ≤ q) (h : HyperplaneIndex s q)
    (S : Finset (Fin (s + 1) → ℝ)) (hS : S ⊆ block s q h) (p : Fin (s + 1) → ℝ)
    (hp : p ∈ block s q h)
    (hx : phi s p ∈ convexHull ℝ (↑(S.image (phi s)) : Set (LiftSpace s))) : p ∈ S := by
  classical
  obtain ⟨w, hw0, hw1, hwz⟩ := Finset.mem_convexHull'.mp hx
  have hinj : Set.InjOn (phi s) (↑S : Set (Fin (s + 1) → ℝ)) :=
    Set.InjOn.mono (show (↑S : Set (Fin (s + 1) → ℝ)) ⊆ ↑(block s q h) from
      fun x hx => hS hx) (phi_injOn s q hs hq h)
  have h1 : ∑ i ∈ S, w (phi s i) = 1 := by
    rw [← hw1, Finset.sum_image hinj]
  have h2 : ∑ i ∈ S, w (phi s i) • phi s i = phi s p := by
    rw [← hwz, Finset.sum_image hinj]
  by_contra hpS
  have hex : ∃ i ∈ S, 0 < w (phi s i) := by
    by_contra hno
    push_neg at hno
    have : ∑ i ∈ S, w (phi s i) ≤ 0 := Finset.sum_nonpos hno
    linarith
  obtain ⟨i, hi, hwi⟩ := hex
  have := convex_pos s q hs hq h S id (fun i => w (phi s i)) p hp (fun i hi => hS hi)
    (fun i hi => hw0 _ (Finset.mem_image_of_mem _ hi)) h1 h2 i hi hwi
  exact hpS (by simpa using this ▸ hi)

end WeakEpsNets.Dev.CBGeo
end

section
set_option autoImplicit false

namespace WeakEpsNets.Dev.CB

open WeakEpsNets.LowerBound WeakEpsNets.Dev.CBGeo

/-- the grid point over `x` in the block of `h` -/
noncomputable def mk (s q : ℕ) (h : HyperplaneIndex s q) (x : Fin s → Fin q) :
    Fin (s + 1) → ℝ :=
  fun i => if hi : i.val < s then (((x ⟨i.val, hi⟩).val + 1 : ℕ) : ℝ)
    else (((∑ j : Fin s, ((h.1 j).val + 1) * ((x j).val + 1) + (h.2.val + 1) : ℕ) : ℕ) : ℝ)
      + tau q

theorem mk_mem (s q : ℕ) (hq : 2 ≤ q) (h : HyperplaneIndex s q) (x : Fin s → Fin q) :
    mk s q h x ∈ block s q h := by
  classical
  rw [mem_block_iff]
  set m : ℕ := ∑ j : Fin s, ((h.1 j).val + 1) * ((x j).val + 1) + (h.2.val + 1) with hm
  have hm1 : 1 ≤ m := by omega
  have hm2 : m ≤ (s + 1) * q ^ 2 := by
    have hsum : ∑ j : Fin s, ((h.1 j).val + 1) * ((x j).val + 1) ≤ ∑ _j : Fin s, q * q := by
      apply Finset.sum_le_sum
      intro j _
      exact Nat.mul_le_mul (by have := (h.1 j).isLt; omega) (by have := (x j).isLt; omega)
    have : ∑ _j : Fin s, q * q = s * q ^ 2 := by simp [sq]
    have hb : h.2.val + 1 ≤ q ^ 2 := by have := h.2.isLt; omega
    rw [hm]; nlinarith
  constructor
  · simp only [shiftedGrid, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨(x, ⟨m - 1, by omega⟩), ?_⟩
    funext i
    by_cases hi : i.val < s
    · simp [mk, hi]
    · simp only [mk, hi, dif_neg, not_false_eq_true]
      have : m - 1 + 1 = m := by omega
      simp [this]
      rw [hm]; push_cast; ring
  · simp only [hyperplane, Set.mem_ofPred_eq]
    simp [mk]

theorem card_block (s q : ℕ) (hq : 2 ≤ q) (h : HyperplaneIndex s q) :
    q ^ s ≤ (block s q h).card := by
  classical
  have : (Finset.univ : Finset (Fin s → Fin q)).card ≤ (block s q h).card := by
    apply Finset.card_le_card_of_injOn (mk s q h)
    · intro x _; exact mk_mem s q hq h x
    · intro x _ y _ hxy
      funext j
      have := congrFun hxy j.castSucc
      simp [mk] at this
      exact Fin.ext this
  simpa using this

theorem card_lifted (s q : ℕ) : (liftedGrid s q).card ≤ (s + 1) * q ^ (s + 2) := by
  classical
  unfold liftedGrid shiftedGrid
  refine (Finset.card_image_le).trans (Finset.card_image_le.trans ?_)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  apply le_of_eq; ring

theorem lifted_sub (s q : ℕ) (h : HyperplaneIndex s q) :
    liftedBlock s q h ⊆ liftedGrid s q := by
  classical
  unfold liftedBlock liftedGrid block
  exact Finset.image_subset_image (Finset.filter_subset _ _)

/-- the main per-hyperplane claim -/
theorem hyper_claim (s q : ℕ) (hs : 1 ≤ s) (hq : 2 ≤ q) (heven : Even q)
    (X : Finset (LiftSpace s))
    (hnet : IsWeakNet (liftedGrid s q) (2 * (s + 1 : ℝ) * (q : ℝ) ^ 2) X)
    (Q : LiftSpace s → HyperplaneIndex s q → Finset (LiftSpace s))
    (hQsub : ∀ z h, Q z h ⊆ liftedBlock s q h)
    (hQhit : ∀ z h, ∀ C ∈ hullFamily s q h, z ∈ C → ∃ x ∈ Q z h, x ∈ C)
    (h : HyperplaneIndex s q) :
    q ^ s / 2 + 1 ≤ (X.biUnion (fun z => Q z h)).card := by
  classical
  by_contra hlt
  push Not at hlt
  have hlt' : (X.biUnion (fun z => Q z h)).card ≤ q ^ s / 2 := by omega
  set U := X.biUnion (fun z => Q z h) with hU
  have hUsub : U ⊆ liftedBlock s q h := fun x hx => by
    obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.1 hx
    exact hQsub z h hz
  have hinj := phi_injOn s q hs hq h
  -- points of the block whose image is not in U
  set G := (block s q h).filter (fun p => phi s p ∉ U) with hG
  set Bad := (block s q h).filter (fun p => phi s p ∈ U) with hBad
  have hBadc : Bad.card ≤ U.card := by
    apply Finset.card_le_card_of_injOn (phi s)
    · intro p hp
      simp only [hBad, Finset.coe_filter, Set.mem_ofPred_eq] at hp
      exact hp.2
    · exact hinj.mono (fun p hp => by simp only [hBad, Finset.coe_filter] at hp; exact hp.1)
  have hGc : q ^ s / 2 ≤ G.card := by
    have hsum : Bad.card + G.card = (block s q h).card :=
      Finset.card_filter_add_card_filter_not (s := block s q h) (fun p => phi s p ∈ U)
    have hb := card_block s q hq h
    have hb2 : q ^ s = 2 * (q ^ s / 2) := by
      have : Even (q ^ s) := heven.pow_of_ne_zero (by omega)
      obtain ⟨m, hm⟩ := this
      omega
    omega
  obtain ⟨S, hSG, hSc⟩ := Finset.exists_subset_card_eq hGc
  have hSB : S ⊆ block s q h := fun p hp => (Finset.mem_filter.1 (hSG hp)).1
  set C : Set (LiftSpace s) := convexHull ℝ (↑(S.image (phi s)) : Set (LiftSpace s)) with hC
  have hCfam : C ∈ hullFamily s q h := by
    unfold hullFamily
    exact ⟨S, hSB, hSc, rfl⟩
  have hSinj := hinj.mono (show (↑S : Set (Fin (s + 1) → ℝ)) ⊆ ↑(block s q h) from
    fun p hp => hSB hp)
  have himg : (S.image (phi s)).card = q ^ s / 2 := by
    rw [Finset.card_image_of_injOn hSinj, hSc]
  have hsubP : S.image (phi s) ⊆ (liftedGrid s q).filter (fun p => p ∈ C) := by
    intro y hy
    rw [Finset.mem_filter]
    refine ⟨?_, subset_convexHull ℝ _ hy⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
    apply lifted_sub s q h
    exact Finset.mem_image_of_mem _ (hSB hp)
  have hPC : ((liftedGrid s q).card : ℝ) / (2 * (s + 1 : ℝ) * (q : ℝ) ^ 2) ≤
      (((liftedGrid s q).filter (fun p => p ∈ C)).card : ℝ) := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have h1 : ((liftedGrid s q).card : ℝ) ≤ ((s + 1 : ℕ) : ℝ) * (q : ℝ) ^ (s + 2) := by
      exact_mod_cast card_lifted s q
    have heven' : Even (q ^ s) := heven.pow_of_ne_zero (by omega)
    obtain ⟨m, hm⟩ := heven'
    have hdiv : q ^ s / 2 = m := by omega
    have hqm : (q : ℝ) ^ s = 2 * m := by exact_mod_cast (by omega : q ^ s = 2 * m)
    have h2 : ((q ^ s / 2 : ℕ) : ℝ) ≤ (((liftedGrid s q).filter (fun p => p ∈ C)).card : ℝ) := by
      rw [← himg]; exact_mod_cast Finset.card_le_card hsubP
    refine le_trans ?_ h2
    rw [hdiv, div_le_iff₀ (by positivity)]
    calc ((liftedGrid s q).card : ℝ) ≤ ((s + 1 : ℕ) : ℝ) * (q : ℝ) ^ (s + 2) := h1
      _ = (m : ℝ) * (2 * (s + 1 : ℝ) * (q : ℝ) ^ 2) := by
        push_cast
        rw [pow_add]
        have : (q : ℝ) ^ s = 2 * m := hqm
        rw [this]; ring
  obtain ⟨z, hzX, hzC⟩ := hnet C (convex_convexHull ℝ _) hPC
  obtain ⟨x, hxQ, hxC⟩ := hQhit z h C hCfam hzC
  have hxU : x ∈ U := Finset.mem_biUnion.2 ⟨z, hzX, hxQ⟩
  have hxB := hQsub z h hxQ
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hxB
  have hpS : p ∈ S := mem_of_mem_hull s q hs hq h S hSB p hp hxC
  exact (Finset.mem_filter.1 (hSG hpS)).2 hxU

end WeakEpsNets.Dev.CB

namespace WeakEpsNets.LowerBound

open WeakEpsNets.Dev.CB in
theorem chk_counting_bound (s q : ℕ) (hs : 1 ≤ s) (hq : 2 ≤ q) (heven : Even q)
    (X : Finset (LiftSpace s))
    (hnet : IsWeakNet (liftedGrid s q) (2 * (s + 1 : ℝ) * (q : ℝ) ^ 2) X) :
    (q : ℝ) ^ (s + 2) / 8 + (q : ℝ) ^ 2 / 4 ≤ (X.card : ℝ) := by
  classical
  choose Q hQsub hQhit hQcard using fun z : LiftSpace s => lemma_2 s q hs hq heven z
  have hcl := fun h => hyper_claim s q hs hq heven X hnet Q hQsub hQhit h
  have hlow : ∑ _h : HyperplaneIndex s q, (q ^ s / 2 + 1) ≤
      ∑ h : HyperplaneIndex s q, (X.biUnion (fun z => Q z h)).card :=
    Finset.sum_le_sum (fun h _ => hcl h)
  have hup : ∑ h : HyperplaneIndex s q, (X.biUnion (fun z => Q z h)).card ≤
      ∑ h : HyperplaneIndex s q, ∑ z ∈ X, (Q z h).card :=
    Finset.sum_le_sum (fun h _ => Finset.card_biUnion_le)
  have hswap : ∑ h : HyperplaneIndex s q, ∑ z ∈ X, (Q z h).card =
      ∑ z ∈ X, ∑ h : HyperplaneIndex s q, (Q z h).card := Finset.sum_comm
  have hz : ∑ z ∈ X, ∑ h : HyperplaneIndex s q, (Q z h).card ≤ ∑ _z ∈ X, 4 * q ^ s :=
    Finset.sum_le_sum (fun z _ => hQcard z)
  have hcardH : Fintype.card (HyperplaneIndex s q) = q ^ s * q ^ 2 := by simp
  have key : q ^ s * q ^ 2 * (q ^ s / 2 + 1) ≤ X.card * (4 * q ^ s) := by
    have := hlow.trans (hup.trans (hswap ▸ hz))
    simpa [hcardH] using this
  have heven' : Even (q ^ s) := heven.pow_of_ne_zero (by omega)
  obtain ⟨m, hm⟩ := heven'
  have hdiv : q ^ s / 2 = m := by omega
  rw [hdiv] at key
  have hqm : (q : ℝ) ^ s = 2 * m := by exact_mod_cast (by omega : q ^ s = 2 * m)
  have keyR : (q : ℝ) ^ s * (q : ℝ) ^ 2 * ((m : ℝ) + 1) ≤ (X.card : ℝ) * (4 * (q : ℝ) ^ s) := by
    exact_mod_cast key
  have hpos : (0 : ℝ) < (q : ℝ) ^ s := by
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  have h3 : (q : ℝ) ^ 2 * ((m : ℝ) + 1) ≤ (X.card : ℝ) * 4 := by
    have : (q : ℝ) ^ s * ((q : ℝ) ^ 2 * ((m : ℝ) + 1)) ≤ (q : ℝ) ^ s * ((X.card : ℝ) * 4) := by
      nlinarith
    exact le_of_mul_le_mul_left this hpos
  rw [pow_add, hqm]
  nlinarith

end WeakEpsNets.LowerBound
end

theorem solution : type_of% @WeakEpsNets.LowerBound.chk_counting_bound := @WeakEpsNets.LowerBound.chk_counting_bound
