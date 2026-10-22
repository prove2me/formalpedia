-- Prove2me | solution 1 for StrategicAlloc.EFXTwoThirds.theorem_4_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T15:35:30.065988+00:00
-- url     : https://prove2.me/submissions/e9ea1d7d-2ebf-4ce2-8ac1-6541eb38c99a

import Mathlib
import Definitions.Def_StrategicAlloc_EFXTwoThirds_Setting

set_option autoImplicit false

namespace P47

lemma fin2_cases (i j k : Fin 2) (h : i ≠ j) : k = i ∨ k = j := by
  revert i j k; decide

lemma sum_le_total {m : ℕ} (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g) (S G : Finset (Fin m))
    (hSG : Disjoint S G) : ∑ g ∈ S, w g ≤ ∑ g, w g - ∑ g ∈ G, w g := by
  have h1 : ∑ g ∈ S ∪ G, w g ≤ ∑ g, w g :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun g _ _ => hw g)
  rw [Finset.sum_union hSG] at h1
  linarith

lemma sum_mono {m : ℕ} (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g) {S T : Finset (Fin m)}
    (h : S ⊆ T) : ∑ g ∈ S, w g ≤ ∑ g ∈ T, w g :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun g _ _ => hw g)

lemma mu_le_of {m : ℕ} (v : Fin 2 → Fin m → ℝ) (i : Fin 2) (B : ℝ)
    (h : ∀ f : Fin m → Fin 2, ∀ S0 S1 : Finset (Fin m), (∀ g, g ∈ S0 ↔ f g = 0) →
      (∀ g, g ∈ S1 ↔ f g = 1) → min (∑ g ∈ S0, v i g) (∑ g ∈ S1, v i g) ≤ B) :
    StrategicAlloc.EFXFour.mu v i ≤ B := by
  unfold StrategicAlloc.EFXFour.mu LittleCharity.MMS.mms
  apply ciSup_le
  intro f
  refine le_trans (le_min (ciInf_le (Set.finite_range _).bddBelow 0)
    (ciInf_le (Set.finite_range _).bddBelow 1)) ?_
  exact h f _ _ (fun g => by simp) (fun g => by simp)

lemma alloc_parts {m : ℕ} (A : Fin 2 → Finset (Fin m))
    (hA : StrategicAlloc.EFXTwoThirds.IsAllocation A) (i j : Fin 2) (hij : i ≠ j) :
    Disjoint (A i) (A j) ∧ A i ∪ A j = Finset.univ := by
  refine ⟨hA.1 hij, ?_⟩
  apply Finset.eq_univ_of_forall
  intro g
  have : g ∈ Finset.univ.biUnion A := by rw [hA.2]; exact Finset.mem_univ g
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp this
  rcases fin2_cases i j k hij with rfl | rfl
  · exact Finset.mem_union_left _ hk
  · exact Finset.mem_union_right _ hk

lemma upd_bid {m : ℕ} (b : Fin 2 → Fin m → ℝ) (hb0 : ∀ k g, 0 ≤ b k g) (i : Fin 2)
    (bs : Fin m → ℝ) (hbs : ∀ g, 0 ≤ bs g) : ∀ k g, 0 ≤ Function.update b i bs k g := by
  intro k g
  by_cases hk : k = i
  · subst hk; simp [hbs]
  · rw [Function.update_of_ne hk]; exact hb0 k g

lemma exists_best {m : ℕ} (M : StrategicAlloc.EFXFour.Mechanism m) (b : Fin 2 → Fin m → ℝ)
    (hb0 : ∀ k g, 0 ≤ b k g) (i : Fin 2) (w : Fin m → ℝ) :
    ∃ bs : Fin m → ℝ, (∀ g, 0 ≤ bs g) ∧ ∀ b' : Fin m → ℝ, (∀ g, 0 ≤ b' g) →
      ∑ g ∈ M (Function.update b i b') i, w g ≤ ∑ g ∈ M (Function.update b i bs) i, w g := by
  classical
  let Sf : Finset (Finset (Fin m)) := Finset.univ.filter
    (fun T => ∃ b' : Fin m → ℝ, (∀ g, 0 ≤ b' g) ∧ M (Function.update b i b') i = T)
  have hne : Sf.Nonempty := ⟨M b i, by
    simp only [Sf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨b i, hb0 i, by rw [Function.update_eq_self]⟩⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image Sf (fun T => ∑ g ∈ T, w g) hne
  simp only [Sf, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  obtain ⟨bs, hbs, rfl⟩ := hT
  refine ⟨bs, hbs, fun b' hb' => hmax _ ?_⟩
  simp only [Sf, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨b', hb', rfl⟩

lemma efx_of_best {m : ℕ} (M : StrategicAlloc.EFXFour.Mechanism m)
    (hM : StrategicAlloc.EFXTwoThirds.IsAlwaysEFXMechanism M) (b : Fin 2 → Fin m → ℝ)
    (hb0 : ∀ k g, 0 ≤ b k g) (i : Fin 2) (w : Fin m → ℝ) (hw : ∀ g, 0 ≤ w g)
    (bs : Fin m → ℝ) (hbs : ∀ g, 0 ≤ bs g)
    (hbest : ∀ b' : Fin m → ℝ, (∀ g, 0 ≤ b' g) →
      ∑ g ∈ M (Function.update b i b') i, w g ≤ ∑ g ∈ M (Function.update b i bs) i, w g) :
    ∀ j, (M (Function.update b i bs) j).Nonempty → ∀ g ∈ M (Function.update b i bs) j, 0 < w g →
      ∑ h ∈ (M (Function.update b i bs) j).erase g, w h ≤
        ∑ h ∈ M (Function.update b i bs) i, w h := by
  classical
  let v' : Fin 2 → Fin m → ℝ := fun k => if k = i then w else 0
  have hv' : ∀ k g, 0 ≤ v' k g := by
    intro k g; by_cases hk : k = i <;> simp [v', hk, hw]
  have hpne : StrategicAlloc.EFXTwoThirds.IsPNE M v' (Function.update b i bs) := by
    refine ⟨upd_bid b hb0 i bs hbs, ?_⟩
    intro k b' hb'
    by_cases hk : k = i
    · subst hk
      simpa [StrategicAlloc.EFXTwoThirds.val, v', Function.update_idem] using hbest b' hb'
    · simp [StrategicAlloc.EFXTwoThirds.val, v', hk]
  have hefx := (hM.2 v' hv').2 _ hpne
  intro j hj g hg hpos
  have := hefx i j hj g hg (by simp [v', hpos])
  simpa [StrategicAlloc.EFXTwoThirds.val, v'] using this

lemma core {m : ℕ} (M : StrategicAlloc.EFXFour.Mechanism m)
    (hM : StrategicAlloc.EFXTwoThirds.IsAlwaysEFXMechanism M)
    (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin 2 → Fin m → ℝ) (hb : StrategicAlloc.EFXTwoThirds.IsPNE M v b)
    (i j : Fin 2) (hij : i ≠ j) (hmu : 0 < StrategicAlloc.EFXFour.mu v i) :
    2 / 3 * StrategicAlloc.EFXFour.mu v i < ∑ g ∈ M b i, v i g := by
  classical
  have hb0 : ∀ k g, 0 ≤ b k g := hb.1
  have hw : ∀ g, 0 ≤ v i g := hv i
  obtain ⟨hD, hU⟩ := alloc_parts (M b) (hM.1 b hb0) i j hij
  have hEFX := (hM.2 v hv).2 b hb
  set x := ∑ g ∈ M b i, v i g with hx
  set y := ∑ g ∈ M b j, v i g with hy
  have htot : ∑ g, v i g = x + y := by rw [hx, hy, ← Finset.sum_union hD, hU]
  have hx0 : 0 ≤ x := Finset.sum_nonneg (fun g _ => hw g)
  have hy0 : 0 ≤ y := Finset.sum_nonneg (fun g _ => hw g)
  -- μ ≤ (x + y) / 2
  have hhalf : StrategicAlloc.EFXFour.mu v i ≤ (x + y) / 2 := by
    apply mu_le_of
    intro f S0 S1 h0 h1
    have hd : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro g g0 g1
      rw [h0] at g0
      rw [h1, g0] at g1
      exact absurd g1 (by decide)
    have := sum_le_total (v i) hw S0 S1 hd
    have := min_le_left (∑ g ∈ S0, v i g) (∑ g ∈ S1, v i g)
    have := min_le_right (∑ g ∈ S0, v i g) (∑ g ∈ S1, v i g)
    linarith
  -- μ ≤ total - v g
  have hsingle : ∀ g, StrategicAlloc.EFXFour.mu v i ≤ x + y - v i g := by
    intro g
    apply mu_le_of
    intro f S0 S1 h0 h1
    rcases fin2_cases 0 1 (f g) (by decide) with hg | hg
    · have hd : Disjoint S1 {g} := by
        rw [Finset.disjoint_singleton_right, h1, hg]; decide
      have := sum_le_total (v i) hw S1 {g} hd
      rw [Finset.sum_singleton] at this
      exact (min_le_right _ _).trans (by linarith)
    · have hd : Disjoint S0 {g} := by
        rw [Finset.disjoint_singleton_right, h0, hg]; decide
      have := sum_le_total (v i) hw S0 {g} hd
      rw [Finset.sum_singleton] at this
      exact (min_le_left _ _).trans (by linarith)
  -- three-goods pigeonhole bound
  have htriple : ∀ a c d : Fin m, a ≠ c → a ≠ d → c ≠ d → ∀ t : ℝ,
      t ≤ v i a + v i c → t ≤ v i a + v i d → t ≤ v i c + v i d →
      StrategicAlloc.EFXFour.mu v i ≤ x + y - t := by
    intro a c d hac had hcd t t1 t2 t3
    apply mu_le_of
    intro f S0 S1 h0 h1
    have pr : ∀ (S : Finset (Fin m)) (p q : Fin m), p ≠ q → p ∉ S → q ∉ S →
        ∑ g ∈ S, v i g ≤ x + y - (v i p + v i q) := by
      intro S p q hpq hp hq
      have hd : Disjoint S {p, q} := by
        rw [Finset.disjoint_left]
        intro g hgS hg
        rw [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl
        · exact hp hgS
        · exact hq hgS
      have := sum_le_total (v i) hw S {p, q} hd
      rw [Finset.sum_pair hpq] at this
      linarith
    have k0 : ∀ p q : Fin m, p ≠ q → f p = 1 → f q = 1 →
        min (∑ g ∈ S0, v i g) (∑ g ∈ S1, v i g) ≤ x + y - (v i p + v i q) := by
      intro p q hpq hp hq
      refine (min_le_left _ _).trans (pr S0 p q hpq ?_ ?_)
      · rw [h0, hp]; decide
      · rw [h0, hq]; decide
    have k1 : ∀ p q : Fin m, p ≠ q → f p = 0 → f q = 0 →
        min (∑ g ∈ S0, v i g) (∑ g ∈ S1, v i g) ≤ x + y - (v i p + v i q) := by
      intro p q hpq hp hq
      refine (min_le_right _ _).trans (pr S1 p q hpq ?_ ?_)
      · rw [h1, hp]; decide
      · rw [h1, hq]; decide
    rcases fin2_cases 0 1 (f a) (by decide) with ha | ha <;>
    rcases fin2_cases 0 1 (f c) (by decide) with hc | hc <;>
    rcases fin2_cases 0 1 (f d) (by decide) with hd | hd <;>
    first
      | linarith [k0 a c hac ha hc] | linarith [k0 a d had ha hd] | linarith [k0 c d hcd hc hd]
      | linarith [k1 a c hac ha hc] | linarith [k1 a d had ha hd] | linarith [k1 c d hcd hc hd]
  by_cases hlt : y < 2 * x
  · linarith
  push_neg at hlt
  by_cases hex : ∃ g ∈ M b j, 0 < v i g
  swap
  · push_neg at hex
    have : y ≤ 0 := Finset.sum_nonpos (fun g hg => hex g hg)
    linarith
  obtain ⟨g, hg, hgpos⟩ := hex
  have hne : (M b j).Nonempty := ⟨g, hg⟩
  have hE : ∀ h ∈ M b j, 0 < v i h → y - v i h ≤ x := by
    intro h hh hpos
    have := hEFX i j hne h hh hpos
    simp only [StrategicAlloc.EFXTwoThirds.val] at this
    rw [Finset.sum_erase_eq_sub hh] at this
    linarith
  have hgx := hE g hg hgpos
  by_cases hex2 : ∃ g' ∈ (M b j).erase g, 0 < v i g'
  swap
  · push_neg at hex2
    have h0 : ∑ h ∈ (M b j).erase g, v i h ≤ 0 := Finset.sum_nonpos hex2
    rw [Finset.sum_erase_eq_sub hg] at h0
    have := hsingle g
    linarith
  obtain ⟨g', hg', hg'pos⟩ := hex2
  have hgg' : g' ≠ g := Finset.ne_of_mem_erase hg'
  have hg'j : g' ∈ M b j := Finset.mem_of_mem_erase hg'
  have hg'x := hE g' hg'j hg'pos
  have hpair : v i g + v i g' ≤ y := by
    have hsub : ({g, g'} : Finset (Fin m)) ⊆ M b j := by
      intro h hh
      rw [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · exact hg
      · exact hg'j
    have := sum_mono (v i) hw hsub
    rw [Finset.sum_pair (Ne.symm hgg')] at this
    linarith
  have hxpos : 0 < x := by linarith
  have hvg : x ≤ v i g := by linarith
  have hvg' : x ≤ v i g' := by linarith
  -- the deviation argument
  let w : Fin m → ℝ := fun h => if h = g ∨ h = g' then 1 else 0
  have hw' : ∀ h, 0 ≤ w h := by
    intro h; simp only [w]; split_ifs <;> norm_num
  obtain ⟨bs, hbs, hbest⟩ := exists_best M b hb0 i w
  have hefxw := efx_of_best M hM b hb0 i w hw' bs hbs hbest
  obtain ⟨hD', hU'⟩ :=
    alloc_parts (M (Function.update b i bs)) (hM.1 _ (upd_bid b hb0 i bs hbs)) i j hij
  have hBR : ∑ h ∈ M (Function.update b i bs) i, v i h ≤ x := hb.2 i bs hbs
  have htot' : ∑ h, v i h = ∑ h ∈ M (Function.update b i bs) i, v i h +
      ∑ h ∈ M (Function.update b i bs) j, v i h := by
    rw [← Finset.sum_union hD', hU']
  have memC : ∀ h, h ∉ M (Function.update b i bs) i → h ∈ M (Function.update b i bs) j := by
    intro h hh
    have : h ∈ M (Function.update b i bs) i ∪ M (Function.update b i bs) j := by
      rw [hU']; exact Finset.mem_univ h
    rcases Finset.mem_union.mp this with h1 | h1
    · exact absurd h1 hh
    · exact h1
  -- sub-claim: one of g, g' lies in agent i's deviation bundle
  have sub : ∀ p ∈ M b j, x ≤ v i p → p ∈ M (Function.update b i bs) i →
      2 / 3 * StrategicAlloc.EFXFour.mu v i < x := by
    intro p hpj hpx hpT
    have hTge : v i p ≤ ∑ h ∈ M (Function.update b i bs) i, v i h := by
      have := sum_mono (v i) hw (Finset.singleton_subset_iff.mpr hpT)
      rwa [Finset.sum_singleton] at this
    have hTerase : ∑ h ∈ (M (Function.update b i bs) i).erase p, v i h ≤ 0 := by
      rw [Finset.sum_erase_eq_sub hpT]; linarith
    have hbestv : ∀ b' : Fin m → ℝ, (∀ g, 0 ≤ b' g) →
        ∑ g ∈ M (Function.update b i b') i, v i g ≤
          ∑ g ∈ M (Function.update b i bs) i, v i g := by
      intro b' hb'
      have : ∑ g ∈ M (Function.update b i b') i, v i g ≤ x := hb.2 i b' hb'
      linarith
    have hefxv := efx_of_best M hM b hb0 i (v i) hw bs hbs hbestv
    obtain ⟨h0, h0A, h0pos⟩ : ∃ h0 ∈ M b i, 0 < v i h0 := by
      by_contra hcon
      push_neg at hcon
      have : x ≤ 0 := Finset.sum_nonpos hcon
      linarith
    have h0p : h0 ≠ p := by
      rintro rfl
      exact Finset.disjoint_left.mp hD h0A hpj
    have h0T : h0 ∉ M (Function.update b i bs) i := by
      intro h0T
      have hmem : h0 ∈ (M (Function.update b i bs) i).erase p := Finset.mem_erase.mpr ⟨h0p, h0T⟩
      have := sum_mono (v i) hw (Finset.singleton_subset_iff.mpr hmem)
      rw [Finset.sum_singleton] at this
      linarith
    have h0C := memC h0 h0T
    have := hefxv j ⟨h0, h0C⟩ h0 h0C h0pos
    rw [Finset.sum_erase_eq_sub h0C] at this
    have hvh0 : x ≤ v i h0 := by linarith
    have hgh0 : g ≠ h0 := by
      rintro rfl; exact Finset.disjoint_left.mp hD h0A hg
    have hg'h0 : g' ≠ h0 := by
      rintro rfl; exact Finset.disjoint_left.mp hD h0A hg'j
    have := htriple g g' h0 (Ne.symm hgg') hgh0 hg'h0 (2 * x) (by linarith) (by linarith)
      (by linarith)
    linarith
  by_cases hgT : g ∈ M (Function.update b i bs) i
  · exact sub g hg hvg hgT
  by_cases hg'T : g' ∈ M (Function.update b i bs) i
  · exact sub g' hg'j hvg' hg'T
  exfalso
  have hgC := memC g hgT
  have hg'C := memC g' hg'T
  have key := hefxw j ⟨g, hgC⟩ g hgC (by simp [w])
  have hT0 : ∑ h ∈ M (Function.update b i bs) i, w h = 0 := by
    apply Finset.sum_eq_zero
    intro h hh
    have h1 : h ≠ g := fun e => hgT (e ▸ hh)
    have h2 : h ≠ g' := fun e => hg'T (e ▸ hh)
    simp [w, h1, h2]
  have hC1 : (1 : ℝ) ≤ ∑ h ∈ (M (Function.update b i bs) j).erase g, w h := by
    have hmem : g' ∈ (M (Function.update b i bs) j).erase g := Finset.mem_erase.mpr ⟨hgg', hg'C⟩
    have := sum_mono w hw' (Finset.singleton_subset_iff.mpr hmem)
    rw [Finset.sum_singleton] at this
    have hw1 : w g' = 1 := by simp [w]
    linarith
  linarith

end P47

open StrategicAlloc.EFXTwoThirds in
theorem solution {m : ℕ} (M : StrategicAlloc.EFXFour.Mechanism m) (hM : IsAlwaysEFXMechanism M)
    (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin 2 → Fin m → ℝ) (hb : IsPNE M v b) :
    ∃ α : ℝ, 2 / 3 < α ∧ StrategicAlloc.EFXFour.IsApproxMMS α v (M b) := by
  have key : ∀ i : Fin 2, ∃ r : ℝ, 2 / 3 < r ∧ ∀ s : ℝ, 2 / 3 < s → s ≤ r →
      s * StrategicAlloc.EFXFour.mu v i ≤ StrategicAlloc.RRFair.val v i (M b i) := by
    intro i
    have hx0 : 0 ≤ StrategicAlloc.RRFair.val v i (M b i) :=
      Finset.sum_nonneg (fun g _ => hv i g)
    by_cases hmu : 0 < StrategicAlloc.EFXFour.mu v i
    · have hij : i ≠ i + 1 := (by decide : ∀ k : Fin 2, k ≠ k + 1) i
      have hc := P47.core M hM v hv b hb i (i + 1) hij hmu
      refine ⟨StrategicAlloc.RRFair.val v i (M b i) / StrategicAlloc.EFXFour.mu v i, ?_, ?_⟩
      · rw [lt_div_iff₀ hmu]; exact hc
      · intro s _ hs
        calc s * StrategicAlloc.EFXFour.mu v i
            ≤ (StrategicAlloc.RRFair.val v i (M b i) / StrategicAlloc.EFXFour.mu v i) *
                StrategicAlloc.EFXFour.mu v i := mul_le_mul_of_nonneg_right hs hmu.le
          _ = StrategicAlloc.RRFair.val v i (M b i) := div_mul_cancel₀ _ hmu.ne'
    · push_neg at hmu
      refine ⟨1, by norm_num, ?_⟩
      intro s hs _
      have : s * StrategicAlloc.EFXFour.mu v i ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hmu
      linarith
  obtain ⟨r0, h0, k0⟩ := key 0
  obtain ⟨r1, h1, k1⟩ := key 1
  refine ⟨min r0 r1, lt_min h0 h1, ?_⟩
  intro i
  rcases P47.fin2_cases 0 1 i (by decide) with rfl | rfl
  · exact k0 _ (lt_min h0 h1) (min_le_left _ _)
  · exact k1 _ (lt_min h0 h1) (min_le_right _ _)
