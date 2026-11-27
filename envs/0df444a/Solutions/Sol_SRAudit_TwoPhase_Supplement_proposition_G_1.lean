-- Prove2me | solution 1 for SRAudit.TwoPhase.Supplement.proposition_G_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:37:56.443744+00:00
-- url     : https://prove2.me/submissions/87c74e98-1970-44ae-8e92-5513a7b0b9eb

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting
import Definitions.Def_SRAudit_TwoPhase_Supplement_AuditMDP
import Definitions.Def_SRAudit_TwoPhase_Supplement_Inaccurate

open SRAudit
open SRAudit.TwoPhase
open SRAudit.TwoPhase.Supplement

open SRAudit.TwoPhase

theorem solution {ι : Type} [DecidableEq ι] (P : Params) (d : ℝ) (hP : StandingG P d)
    (π : Network ι → ℝ) (ξ : Policy ι) (hξ : IsAdmissible ξ) :
    ∀ γ : State ι, ∃ ξ' : Policy ι, IsAdmissible ξ' ∧
      (∀ (γ' : State ι) (i j : Supplier ι), ξ' γ' = .ar i → ξ' (vet γ' i) ≠ .ad j) ∧
      VpolG P d ∅ π ξ γ ≤ VpolG P d ∅ π ξ' γ := by
        classical
        obtain ⟨⟨ha, hr, hu0, hu1, -, -, -⟩, hd0, hd1⟩ := hP
        have hc : 0 ≤ P.u * d * P.r := by positivity
        have hp0 : 0 ≤ P.u * d := by positivity
        have hp1 : P.u * d ≤ 1 := by nlinarith
        unfold VpolG
        generalize ppValueG P d ∅ π = term
        generalize P.u * d * P.r = c at *
        generalize P.u * d = p at *
        generalize P.a = a at *
        -- state equality
        have stEq : ∀ s t : State ι, s.g = t.g → s.U = t.U → s = t := by
          rintro ⟨g, U, h⟩ ⟨g', U', h'⟩ hg hU
          simp only at hg hU
          subst hg; subst hU; rfl
        have vv : ∀ (γ : State ι) (i j : Supplier ι), vet (vet γ i) j = vet (vet γ j) i :=
          fun γ i j => stEq _ _ rfl (by simp [vet, Finset.erase_right_comm])
        have vd : ∀ (γ : State ι) (i j : Supplier ι), vet (drop γ j) i = drop (vet γ i) j := by
          intro γ i j
          refine stEq _ _ rfl ?_
          show (γ.U \ γ.g.dependents j).erase i = γ.U.erase i \ γ.g.dependents j
          rw [Finset.erase_sdiff_comm]
        have vnm : ∀ (γ : State ι) (i : Supplier ι), i ∉ γ.U → vet γ i = γ := by
          intro γ i hi
          refine stEq _ _ rfl ?_
          show γ.U.erase i = γ.U
          exact Finset.erase_eq_of_notMem hi
        set V := Vgen a c p term with hV
        set Q := Qgen a c p term with hQ
        have Veq : ∀ γ : State ι, V γ = if h : γ.U.Nonempty then
            max (term γ) (γ.U.attach.sup' (by simpa using h) (fun i =>
              max (-a - c + V (vet γ i.val))
                  (-a + (1 - p) * V (vet γ i.val) + p * V (drop γ i.val)))) else term γ := by
          intro γ; rw [hV, Vgen]
        -- (B) every admissible action is bounded by V
        have hB : ∀ (γ : State ι) (x : Action ι), Admissible γ x → Q γ x ≤ V γ := by
          intro γ x hx
          have hne : γ.U.Nonempty → True := fun _ => trivial
          cases x with
          | pp =>
            show term γ ≤ V γ
            rw [Veq]; split_ifs
            · exact le_max_left _ _
            · exact le_rfl
          | ar i =>
            have hi : i ∈ γ.U := hx
            show (if i ∈ γ.U then -a - c + V (vet γ i) else 0) ≤ V γ
            rw [if_pos hi, Veq γ, dif_pos ⟨i, hi⟩]
            refine le_trans ?_ (le_max_right _ _)
            refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_attach _ ⟨i, hi⟩))
            exact le_max_left _ _
          | ad i =>
            have hi : i ∈ γ.U := hx
            show (if i ∈ γ.U then -a + (1 - p) * V (vet γ i) + p * V (drop γ i) else 0) ≤ V γ
            rw [if_pos hi, Veq γ, dif_pos ⟨i, hi⟩]
            refine le_trans ?_ (le_max_right _ _)
            refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_attach _ ⟨i, hi⟩))
            exact le_max_right _ _
        -- (C) some admissible action attains V
        have hC : ∀ γ : State ι, ∃ x, Admissible γ x ∧ Q γ x = V γ := by
          intro γ
          by_cases h : γ.U.Nonempty
          · have e := Veq γ
            rw [dif_pos h] at e
            obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' (Finset.attach_nonempty_iff.mpr h) (fun i : γ.U =>
              max (-a - c + V (vet γ i.val))
                  (-a + (1 - p) * V (vet γ i.val) + p * V (drop γ i.val)))
            rw [hk] at e
            rcases max_choice (term γ) (max (-a - c + V (vet γ k.val))
                  (-a + (1 - p) * V (vet γ k.val) + p * V (drop γ k.val))) with h1 | h1
            · exact ⟨.pp, trivial, by rw [e, h1]; rfl⟩
            · rw [h1] at e
              rcases max_choice (-a - c + V (vet γ k.val))
                  (-a + (1 - p) * V (vet γ k.val) + p * V (drop γ k.val)) with h2 | h2
              · refine ⟨.ar k.val, k.property, ?_⟩
                rw [e, h2]; show (if k.val ∈ γ.U then _ else _) = _; rw [if_pos k.property]
              · refine ⟨.ad k.val, k.property, ?_⟩
                rw [e, h2]; show (if k.val ∈ γ.U then _ else _) = _; rw [if_pos k.property]
          · refine ⟨.pp, trivial, ?_⟩
            rw [Veq, dif_neg h]; rfl
        -- the tie-breaking policy
        let ξ' : Policy ι := fun γ =>
          if Q γ .pp = V γ then .pp
          else if h : ∃ j, j ∈ γ.U ∧ Q γ (.ad j) = V γ then .ad h.choose
          else if h2 : ∃ i, i ∈ γ.U ∧ Q γ (.ar i) = V γ then .ar h2.choose
          else .pp
        have hopt : ∀ γ, Admissible γ (ξ' γ) ∧ Q γ (ξ' γ) = V γ := by
          intro γ
          simp only [ξ']
          split_ifs with h0 h1 h2
          · exact ⟨trivial, h0⟩
          · exact h1.choose_spec
          · exact ⟨h2.choose_spec.1, h2.choose_spec.2⟩
          · exfalso
            obtain ⟨x, hx, hq⟩ := hC γ
            cases x with
            | pp => exact h0 hq
            | ar i => exact h2 ⟨i, hx, hq⟩
            | ad i => exact h1 ⟨i, hx, hq⟩
        have harN : ∀ γ i, ξ' γ = .ar i → ∀ j ∈ γ.U, Q γ (.ad j) ≠ V γ := by
          intro γ i h j hj hq
          simp only [ξ'] at h
          split_ifs at h with h0 h1
          exact h1 ⟨j, hj, hq⟩
        have hD : ∀ (δ : State ι) (i : Supplier ι), -a - c + V (vet δ i) ≤ V δ := by
          intro δ i
          by_cases hi : i ∈ δ.U
          · have := hB δ (.ar i) hi
            simpa [hQ, Qgen, hi] using this
          · rw [vnm δ i hi]; linarith
        refine fun γ0 => ⟨ξ', fun γ => (hopt γ).1, ?_, ?_⟩
        · intro γ i j hi hj
          have h1 := hopt γ
          have h2 := hopt (vet γ i)
          rw [hi] at h1
          rw [hj] at h2
          obtain ⟨hiU, hQi⟩ := h1
          obtain ⟨hjU, hQj⟩ := h2
          have hiU' : i ∈ γ.U := hiU
          have hjU' : j ∈ (γ.U).erase i := hjU
          have hji : j ≠ i := Finset.ne_of_mem_erase hjU'
          have hjU'' : j ∈ γ.U := Finset.mem_of_mem_erase hjU'
          apply harN γ i hi j hjU''
          apply le_antisymm (hB γ (.ad j) hjU'')
          have e1 : V γ = -a - c + V (vet γ i) := by
            rw [← hQi]; show (if i ∈ γ.U then _ else _) = _; rw [if_pos hiU']
          have e2 : V (vet γ i) = -a + (1 - p) * V (vet (vet γ i) j) + p * V (drop (vet γ i) j) := by
            have hjv : j ∈ (vet γ i).U := hjU
            rw [← hQj]; show (if j ∈ (vet γ i).U then _ else _) = _; rw [if_pos hjv]
          have b1 : -a - c + V (vet (vet γ i) j) ≤ V (vet γ j) := by
            rw [vv]; exact hD _ _
          have b2 : -a - c + V (drop (vet γ i) j) ≤ V (drop γ j) := by
            rw [← vd]; exact hD _ _
          show V γ ≤ (if j ∈ γ.U then -a + (1 - p) * V (vet γ j) + p * V (drop γ j) else 0)
          rw [if_pos hjU'']
          have m1 := mul_le_mul_of_nonneg_left b1 (by linarith : (0:ℝ) ≤ 1 - p)
          have m2 := mul_le_mul_of_nonneg_left b2 hp0
          nlinarith
        · -- values
          have hval : ∀ n, ∀ γ : State ι, γ.U.card = n →
              Vpolgen a c p term ξ γ ≤ V γ ∧ Vpolgen a c p term ξ' γ = V γ := by
            intro n
            induction n using Nat.strong_induction_on with
            | _ n ih =>
            intro γ hγ
            have IH : ∀ δ : State ι, δ.U.card < γ.U.card →
                Vpolgen a c p term ξ δ ≤ V δ ∧ Vpolgen a c p term ξ' δ = V δ :=
              fun δ hδ => ih _ (hγ ▸ hδ) δ rfl
            have hT : term γ ≤ V γ := hB γ .pp trivial
            constructor
            · rw [Vpolgen]
              rcases hx : ξ γ with _ | i | i
              · exact hT
              · dsimp only
                split_ifs with hi
                · have h1 := (IH _ (vet_U_card_lt γ i hi)).1
                  have h2 := hB γ (.ar i) hi
                  simp only [hQ, Qgen, if_pos hi] at h2
                  linarith
                · exact hT
              · dsimp only
                split_ifs with hi
                · have h1 := (IH _ (vet_U_card_lt γ i hi)).1
                  have h1' := (IH _ (drop_U_card_lt γ i hi)).1
                  have h2 := hB γ (.ad i) hi
                  simp only [hQ, Qgen, if_pos hi] at h2
                  have m1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - p)
                  have m2 := mul_le_mul_of_nonneg_left h1' hp0
                  linarith
                · exact hT
            · obtain ⟨hadm, hq⟩ := hopt γ
              rw [Vpolgen]
              rcases hx : ξ' γ with _ | i | i
              · rw [hx] at hq; exact hq
              · rw [hx] at hq hadm
                have hi : i ∈ γ.U := hadm
                dsimp only
                rw [if_pos hi, (IH _ (vet_U_card_lt γ i hi)).2, ← hq]
                simp only [hQ, Qgen, if_pos hi]
                rfl
              · rw [hx] at hq hadm
                have hi : i ∈ γ.U := hadm
                dsimp only
                rw [if_pos hi, (IH _ (vet_U_card_lt γ i hi)).2, (IH _ (drop_U_card_lt γ i hi)).2, ← hq]
                simp only [hQ, Qgen, if_pos hi]
                rfl
          have := hval _ γ0 rfl
          rw [this.2]; exact this.1
