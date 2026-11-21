-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_withSeminorms_sum
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T03:07:54.882114+00:00
-- url     : https://prove2.me/submissions/bf977a9a-52c4-41d9-8e98-beb36bcced54

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L482-L493
import Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms
import Theorems.Thm_RiemannMasullo_elementarySchwartzBound_zero
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
open Filter Topology
open scoped ENNReal
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
theorem solution :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F) ℕ,
      WithSeminorms p ∧ (∀ N f, p N f = 0 ↔ f = 0) ∧
        ∀ N f, p N f =
          ∑ i : (Fin m → Fin (N + 1)) × (Fin m → Fin (N + 1)) ×
                (Fin n → Fin (N + 1)) × (Fin r → Fin (N + 1)),
            if (∑ k, (i.1 k).val) ≤ N ∧ (∑ k, (i.2.1 k).val) ≤ N ∧
                (∑ k, (i.2.2.1 k).val) ≤ N ∧ (∑ k, (i.2.2.2 k).val) ≤ N then
              elementarySchwartzSeminorm
                (fun k ↦ (i.1 k).val, fun k ↦ (i.2.1 k).val,
                  fun k ↦ (i.2.2.1 k).val, fun k ↦ (i.2.2.2 k).val) f
            else 0 := by
  classical
  let E := ElementarySchwartz m n r F
  let I := (Fin m → ℕ) × (Fin m → ℕ) × (Fin n → ℕ) × (Fin r → ℕ)
  let J (N : ℕ) := (Fin m → Fin (N+1)) × (Fin m → Fin (N+1)) ×
    (Fin n → Fin (N+1)) × (Fin r → Fin (N+1))
  let P : I → Seminorm ℂ E := elementarySchwartzSeminorm
  let idx (N : ℕ) (i : J N) : I :=
    (fun k => (i.1 k).val, fun k => (i.2.1 k).val, fun k => (i.2.2.1 k).val, fun k => (i.2.2.2 k).val)
  let good (N : ℕ) (i : I) : Prop := (∑ k, i.1 k) ≤ N ∧ (∑ k, i.2.1 k) ≤ N ∧
    (∑ k, i.2.2.1 k) ≤ N ∧ (∑ k, i.2.2.2 k) ≤ N
  let term (N : ℕ) (i : J N) : Seminorm ℂ E := if good N (idx N i) then P (idx N i) else 0
  let Q (N : ℕ) : Seminorm ℂ E := ∑ i : J N, term N i
  have hp : WithSeminorms P := elementarySchwartz_withSeminorms
  have hm (N : ℕ) (i : J N) (hg : good N (idx N i)) : P (idx N i) ≤ Q N := by
    have h := (Finset.le_sup (f:=term N) (Finset.mem_univ i)).trans
      (Seminorm.finset_sup_le_sum (term N) Finset.univ)
    simpa only [Q, term, if_pos hg] using h
  have hdom (i : I) : ∃ N, P i ≤ Q N := by
    let N := (∑ k,i.1 k)+(∑ k,i.2.1 k)+(∑ k,i.2.2.1 k)+(∑ k,i.2.2.2 k)
    have hsum {d : ℕ} (a : Fin d → ℕ) (k : Fin d) : a k ≤ ∑ l,a l :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    let t : J N := (fun k => ⟨i.1 k,by have := hsum i.1 k; dsimp [N]; omega⟩,
      fun k => ⟨i.2.1 k,by have := hsum i.2.1 k; dsimp [N]; omega⟩,
      fun k => ⟨i.2.2.1 k,by have := hsum i.2.2.1 k; dsimp [N]; omega⟩,
      fun k => ⟨i.2.2.2 k,by have := hsum i.2.2.2 k; dsimp [N]; omega⟩)
    have hi : idx N t = i := rfl
    refine ⟨N,hi ▸ hm N t ?_⟩
    rw [hi]; dsimp [good,N]; omega
  refine ⟨Q,?_,?_,?_⟩
  · apply (SeminormFamily.withSeminorms_iff_nhds_eq_iInf Q).mpr
    apply le_antisymm
    · apply le_iInf
      intro N
      apply Filter.tendsto_iff_comap.mp
      have hcont : Continuous (Q N) := by
        apply Seminorm.continuous_finsetSum
        intro i _
        dsimp only [term]
        split_ifs
        · exact hp.continuous_seminorm _
        · exact continuous_const
      exact hcont.tendsto' 0 0 (map_zero _)
    · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf P).mp hp]
      apply le_iInf
      intro i
      obtain ⟨N,hN⟩ := hdom i
      apply le_trans (iInf_le _ N)
      apply Filter.tendsto_iff_comap.mp
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (Filter.tendsto_comap : Filter.Tendsto (Q N) (Filter.comap (Q N) (𝓝 0)) (𝓝 0))
        (fun f => apply_nonneg (P i) f) hN
  · intro N f
    refine ⟨fun hz => ?_, fun h => by simp [h]⟩
    let t : J N := (fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0)
    have ht : good N (idx N t) := by simp [good,idx,t]
    have hq := hm N t ht f
    rw [hz] at hq
    have hzero := le_antisymm hq (apply_nonneg (P (idx N t)) f)
    change (elementarySchwartzBound f.val (0,0,0,0)).toReal = 0 at hzero
    have hfin := (f.property.2 (0,0,0,0)).ne
    have hz' := ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right hfin
    rw [elementarySchwartzBound_zero] at hz'
    apply Subtype.ext
    funext g
    change f.val g = 0
    have hb := le_iSup (fun x => (‖f.val x‖₊ : ℝ≥0∞)) g
    rw [hz'] at hb
    simpa using (le_antisymm hb (by positivity))
  · intro N f
    change FunLike.coeAddMonoidHom _ _ _ (∑ i : J N, term N i) f = _
    rw [map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    change (term N i) f = if good N (idx N i) then (P (idx N i)) f else 0
    by_cases h : good N (idx N i) <;> simp [term,h]
