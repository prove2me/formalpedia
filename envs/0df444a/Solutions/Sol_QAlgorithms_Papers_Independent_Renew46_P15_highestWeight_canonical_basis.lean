-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P15.highestWeight_canonical_basis
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:36:16.030985+00:00
-- url     : https://prove2.me/submissions/4adfe308-56bb-421c-9f31-3226362f18c3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

attribute [local instance] Classical.propDecidable

namespace X6R15C

open QAlgorithms.Papers.Independent.Renew46.P15 Submodule Set

variable {m d : ℕ}

/-- `k` is the leading (first nonzero) coordinate of `x`. -/
def IsLead (x : Fin d → ℝ) (k : Fin d) : Prop := x k ≠ 0 ∧ ∀ j, j < k → x j = 0

theorem lead_unique {x : Fin d → ℝ} {k k' : Fin d} (h : IsLead x k) (h' : IsLead x k') :
    k = k' := by
  rcases lt_trichotomy k k' with hk | hk | hk
  · exact absurd (h'.2 k hk) h.1
  · exact hk
  · exact absurd (h.2 k' hk) h'.1

theorem exists_lead {x : Fin d → ℝ} (hx : x ≠ 0) : ∃ k, IsLead x k := by
  classical
  have hne : (Finset.univ.filter fun k => x k ≠ 0).Nonempty := by
    by_contra h
    apply hx
    funext k
    by_contra hk
    exact h ⟨k, by simpa using hk⟩
  refine ⟨(Finset.univ.filter fun k => x k ≠ 0).min' hne, ?_, ?_⟩
  · have := Finset.min'_mem _ hne
    simpa using this
  · intro j hj
    by_contra hxj
    have := Finset.min'_le (Finset.univ.filter fun k => x k ≠ 0) j (by simpa using hxj)
    exact absurd hj (not_lt.2 this)

/-- coordinates of a combination of RREF rows at the pivots -/
theorem comb_pivot (b : Matrix (Fin m) (Fin d) ℝ) (p : Fin m → Fin d)
    (h1 : ∀ i, b i (p i) = 1) (h3 : ∀ i j, i ≠ j → b j (p i) = 0) (c : Fin m → ℝ) (j : Fin m) :
    (∑ i, c i • b i) (p j) = c j := by
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [h1]
  · intro i _ hij; simp [h3 j i (Ne.symm hij)]
  · simp

theorem lead_comb (b : Matrix (Fin m) (Fin d) ℝ) (p : Fin m → Fin d) (hp : StrictMono p)
    (h1 : ∀ i, b i (p i) = 1) (h2 : ∀ i k, k < p i → b i k = 0)
    (h3 : ∀ i j, i ≠ j → b j (p i) = 0) (c : Fin m → ℝ) (hc : c ≠ 0) :
    ∃ i, IsLead (∑ i, c i • b i) (p i) := by
  classical
  have hne : (Finset.univ.filter fun i => c i ≠ 0).Nonempty := by
    by_contra h
    apply hc
    funext k
    by_contra hk
    exact h ⟨k, by simpa using hk⟩
  set i0 := (Finset.univ.filter fun i => c i ≠ 0).min' hne
  have hi0 : c i0 ≠ 0 := by simpa using Finset.min'_mem _ hne
  have hmin : ∀ i, c i ≠ 0 → i0 ≤ i := fun i hi =>
    Finset.min'_le (Finset.univ.filter fun i => c i ≠ 0) i (by simpa using hi)
  refine ⟨i0, ?_, ?_⟩
  · rw [comb_pivot b p h1 h3]; exact hi0
  · intro k hk
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hci : c i = 0
    · simp [hci]
    · have : i0 ≤ i := hmin i hci
      have : k < p i := lt_of_lt_of_le hk (hp.monotone this)
      simp [h2 i k this]

theorem rref_li (b : Matrix (Fin m) (Fin d) ℝ) (p : Fin m → Fin d)
    (h1 : ∀ i, b i (p i) = 1) (h3 : ∀ i j, i ≠ j → b j (p i) = 0) :
    LinearIndependent ℝ (fun i => b i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have := comb_pivot b p h1 h3 c j
  rw [hc] at this
  simpa using this.symm

/-- the set of leads of nonzero vectors of the row space of an RREF matrix is the range
of its pivot map -/
theorem leads_eq (b : Matrix (Fin m) (Fin d) ℝ) (p : Fin m → Fin d) (hp : StrictMono p)
    (h1 : ∀ i, b i (p i) = 1) (h2 : ∀ i k, k < p i → b i k = 0)
    (h3 : ∀ i j, i ≠ j → b j (p i) = 0) :
    {k | ∃ x ∈ span ℝ (range b), IsLead x k} = range p := by
  ext k
  constructor
  · rintro ⟨x, hx, hk⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
    have hc : c ≠ 0 := by
      rintro rfl
      exact hk.1 (by simp)
    obtain ⟨i, hi⟩ := lead_comb b p hp h1 h2 h3 c hc
    exact ⟨i, lead_unique hi hk⟩
  · rintro ⟨i, rfl⟩
    exact ⟨b i, subset_span ⟨i, rfl⟩, by rw [h1]; exact one_ne_zero, h2 i⟩

theorem rref_unique (b b' : Matrix (Fin m) (Fin d) ℝ) (hb : IsRREF b) (hb' : IsRREF b')
    (h : span ℝ (range b) = span ℝ (range b')) : b = b' := by
  obtain ⟨p, hp, h1, h2, h3⟩ := hb
  obtain ⟨p', hp', h1', h2', h3'⟩ := hb'
  have hpp : p = p' := by
    rw [← hp.range_inj hp', ← leads_eq b p hp h1 h2 h3, ← leads_eq b' p' hp' h1' h2' h3', h]
  subst hpp
  funext i
  have hmem : b i - b' i ∈ span ℝ (range b) :=
    sub_mem (subset_span ⟨i, rfl⟩) (h ▸ subset_span ⟨i, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  have hc0 : c = 0 := by
    funext j
    have := comb_pivot b p h1 h3 c j
    rw [hc] at this
    rw [← this]
    simp only [Pi.sub_apply, Pi.zero_apply]
    by_cases hij : i = j
    · subst hij; rw [h1, h1']; ring
    · rw [h3 j i (Ne.symm hij), h3' j i (Ne.symm hij)]; ring
  rw [hc0] at hc
  have : b i - b' i = 0 := by rw [← hc]; simp
  exact sub_eq_zero.1 this

/-- vectors with pairwise distinct leads are linearly independent -/
theorem li_of_leads {ι : Type*} [Fintype ι] (w : ι → Fin d → ℝ) (ℓ : ι → Fin d)
    (hℓ : Function.Injective ℓ) (hw : ∀ s, IsLead (w s) (ℓ s)) : LinearIndependent ℝ w := by
  classical
  rw [Fintype.linearIndependent_iff]
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc, ⟨s1, hs1⟩⟩ := hcon
  have hne : (Finset.univ.filter fun s => c s ≠ 0).Nonempty := ⟨s1, by simpa using hs1⟩
  -- the minimal lead among nonzero coefficients
  obtain ⟨s0, hs0, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun s => c s ≠ 0) ℓ hne
  have hcs0 : c s0 ≠ 0 := by simpa using hs0
  have := congrFun hc (ℓ s0)
  rw [Finset.sum_apply, Finset.sum_eq_single s0] at this
  · simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hcs0 h
    · exact (hw s0).1 h
  · intro s _ hs
    by_cases hcs : c s = 0
    · simp [hcs]
    · have hle : ℓ s0 ≤ ℓ s := hmin s (by simpa using hcs)
      have hlt : ℓ s0 < ℓ s := lt_of_le_of_ne hle (fun e => hs (hℓ e.symm))
      simp [(hw s).2 _ hlt]
  · simp

theorem rref_exists (V : Submodule ℝ (Fin d → ℝ)) (hV : Module.finrank ℝ V = m) :
    ∃ b : Matrix (Fin m) (Fin d) ℝ, IsRREF b ∧ span ℝ (range b) = V := by
  classical
  set S : Finset (Fin d) := Finset.univ.filter fun k => ∃ x ∈ V, IsLead x k with hS
  have hSmem : ∀ k, k ∈ S ↔ ∃ x ∈ V, IsLead x k := by intro k; simp [hS]
  -- card S ≤ m
  have hle : S.card ≤ m := by
    choose w hwV hw using fun s : S => (hSmem s).1 s.2
    have hli : LinearIndependent ℝ w :=
      li_of_leads w (fun s => (s : Fin d)) Subtype.coe_injective hw
    have h1 := finrank_span_eq_card hli
    have h2 : span ℝ (range w) ≤ V := span_le.2 (by rintro _ ⟨s, rfl⟩; exact hwV s)
    have h3 := Submodule.finrank_mono h2
    rw [h1, hV] at h3
    simpa using h3
  -- injectivity of restriction to S
  let φS : V →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun x s => (x : Fin d → ℝ) s
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have hφS : Function.Injective φS := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hx0' : (x : Fin d → ℝ) ≠ 0 := fun h => hx0 (Subtype.ext h)
    obtain ⟨k, hk⟩ := exists_lead hx0'
    have hkS : k ∈ S := (hSmem k).2 ⟨x, x.2, hk⟩
    have := congrFun hx ⟨k, hkS⟩
    exact hk.1 this
  have hge : m ≤ S.card := by
    have := LinearMap.finrank_le_finrank_of_injective hφS
    rw [hV] at this
    simpa using this
  have hcard : S.card = m := le_antisymm hle hge
  set p := S.orderEmbOfFin hcard with hpdef
  have hpS : ∀ i, p i ∈ S := fun i => S.orderEmbOfFin_mem hcard i
  have hrange : ∀ k ∈ S, ∃ i, p i = k := by
    intro k hk
    have : k ∈ Set.range p := by
      rw [hpdef, Finset.range_orderEmbOfFin]; exact hk
    exact this
  -- pivot map
  let φ : V →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun x i => (x : Fin d → ℝ) (p i)
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hx0' : (x : Fin d → ℝ) ≠ 0 := fun h => hx0 (Subtype.ext h)
    obtain ⟨k, hk⟩ := exists_lead hx0'
    obtain ⟨i, hi⟩ := hrange k ((hSmem k).2 ⟨x, x.2, hk⟩)
    have := congrFun hx i
    apply hk.1
    rw [← hi]; exact this
  have hφs : Function.Surjective φ := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hφ
    · simp [hV]
  choose r hr using fun i : Fin m => hφs (Pi.single i 1)
  have hr' : ∀ i j, (r i : Fin d → ℝ) (p j) = (Pi.single i (1 : ℝ) : Fin m → ℝ) j :=
    fun i j => congrFun (hr i) j
  let b : Matrix (Fin m) (Fin d) ℝ := fun i => (r i : Fin d → ℝ)
  have h1 : ∀ i, b i (p i) = 1 := by intro i; simp [b, hr']
  have h3 : ∀ i j, i ≠ j → b j (p i) = 0 := by
    intro i j hij; simp [b, hr', Pi.single_apply, hij]
  have h2 : ∀ i k, k < p i → b i k = 0 := by
    intro i k hk
    have hb0 : b i ≠ 0 := by
      intro h; have := h1 i; rw [h] at this; simp at this
    obtain ⟨k0, hk0⟩ := exists_lead hb0
    obtain ⟨j, hj⟩ := hrange k0 ((hSmem k0).2 ⟨b i, (r i).2, hk0⟩)
    have hji : j = i := by
      by_contra hne
      exact hk0.1 (by rw [← hj]; exact h3 j i hne)
    subst hji
    rw [hj] at hk
    exact hk0.2 k (hj ▸ hk)
  refine ⟨b, ⟨p, p.strictMono, h1, h2, h3⟩, ?_⟩
  apply le_antisymm
  · exact span_le.2 (by rintro _ ⟨i, rfl⟩; exact (r i).2)
  · intro x hx
    have hdiff : φ (⟨x, hx⟩ - ∑ i, (x (p i)) • r i) = 0 := by
      funext j
      rw [map_sub, map_sum]
      simp only [map_smul, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      rw [Finset.sum_eq_single j]
      · rw [hr j]; simp [φ]
      · intro i _ hij; rw [hr i]; simp [Pi.single_apply, Ne.symm hij]
      · simp
    have := hφ (hdiff.trans (map_zero φ).symm)
    rw [sub_eq_zero] at this
    have hx' : x = ∑ i, x (p i) • b i := by
      have := congrArg Subtype.val this
      simpa [b] using this
    rw [hx']
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)

end X6R15C

namespace X6R15CS
open QAlgorithms.Papers.Independent.Renew46.P15 Submodule Set X6R15C

theorem span_eRow {N m : ℕ} (a : Matrix (Fin m) (Fin N) ℝ) :
    span ℝ (range (euclideanRow a)) =
      (span ℝ (range a)).map (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.toLinearMap := by
  rw [map_span]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨a y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, rfl⟩

theorem span_eRow_iff {N m : ℕ} (a b : Matrix (Fin m) (Fin N) ℝ) :
    span ℝ (range (euclideanRow b)) = span ℝ (range (euclideanRow a)) ↔
      span ℝ (range b) = span ℝ (range a) := by
  rw [span_eRow, span_eRow]
  exact (Submodule.map_injective_of_injective
    (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm.injective).eq_iff

end X6R15CS

open QAlgorithms.Papers.Independent.Renew46.P15 Submodule Set X6R15C X6R15CS in
theorem solution {n r m : ℕ} (s sPrime : GTTopRow n)
    (t : Fin r → GTTopRow n) (c : CGTable s sPrime t) (j : Fin r)
    (order : Fin (Fintype.card (Pattern s × Pattern sPrime)) ≃
      (Pattern s × Pattern sPrime))
    (a : Matrix (Fin m) (Fin (Fintype.card (Pattern s × Pattern sPrime))) ℝ)
    (independent : LinearIndependent ℝ (fun i p => a i (order.symm p)))
    (complete : Submodule.span ℝ (Set.range (fun i p => a i (order.symm p))) =
      highestKernel s sPrime (t j)) :
    ∃! b : Matrix (Fin m) (Fin (Fintype.card (Pattern s × Pattern sPrime))) ℝ,
      IsRREF b ∧
      Submodule.span ℝ (Set.range (euclideanRow b)) =
        Submodule.span ℝ (Set.range (euclideanRow a)) ∧
      Orthonormal ℝ (canonicalRows b) ∧
      Submodule.span ℝ (Set.range (canonicalRows b)) =
        Submodule.span ℝ (Set.range (euclideanRow a)) ∧
      ∀ i, InnerProductSpace.gramSchmidt ℝ (euclideanRow b) i ≠ 0 := by
  have hli : LinearIndependent ℝ (fun i => a i) := by
    have : LinearIndependent ℝ ((LinearMap.funLeft ℝ ℝ order.symm) ∘ (fun i => a i)) :=
      independent
    exact this.of_comp _
  have hfr : Module.finrank ℝ (span ℝ (range a)) = m := by
    rw [finrank_span_eq_card hli]; simp
  obtain ⟨b, hb, hspan⟩ := rref_exists (span ℝ (range a)) hfr
  have hbli : LinearIndependent ℝ (euclideanRow b) := by
    obtain ⟨p, _, h1, _, h3⟩ := hb
    have := rref_li b p h1 h3
    exact this.map' (WithLp.linearEquiv 2 ℝ (Fin (Fintype.card (Pattern s × Pattern sPrime)) → ℝ)).symm.toLinearMap
      (WithLp.linearEquiv 2 ℝ (Fin (Fintype.card (Pattern s × Pattern sPrime)) → ℝ)).symm.ker
  have hsp : span ℝ (range (euclideanRow b)) = span ℝ (range (euclideanRow a)) :=
    (span_eRow_iff a b).2 hspan
  refine ⟨b, ⟨hb, hsp, InnerProductSpace.gramSchmidtNormed_orthonormal hbli, ?_,
    fun i => InnerProductSpace.gramSchmidt_ne_zero i hbli⟩, ?_⟩
  · unfold canonicalRows
    rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt, hsp]
  · rintro b' ⟨hb', hsp', -⟩
    apply rref_unique b' b hb' hb
    rw [(span_eRow_iff a b').1 hsp', hspan]
