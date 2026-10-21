-- Prove2me | solution 1 for ShortestGCS.MICP.proof_5_7_path_and_cycles
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:37:09.241259+00:00
-- url     : https://prove2.me/submissions/56d1805b-d22b-4ad5-be2f-c0e8f91723a0

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_ShortestGCS_MICP_Setting

set_option autoImplicit false
open ShortestGCS.MICP

def SgmGood {V : Type*} (F : V → V → Prop) (t : V) (l : List V) : Prop :=
  l.getLast? = some t ∧ l.Nodup ∧ ∀ i (h : i + 1 < l.length), F l[i] l[i + 1]

theorem sgm_build {V : Type*} [Fintype V] [DecidableEq V] (F : V → V → Prop) (s t : V)
    (hout_t : ∀ w, ¬ F t w)
    (hout_uniq : ∀ v a b, F v a → F v b → a = b)
    (hex_t : ∃ u, F u t)
    (hcons : ∀ v, v ≠ s → v ≠ t → ∀ b, F v b → ∃ a, F a v) :
    ∃ l : List V, l.head? = some s ∧ SgmGood F t l := by
  have H : ∀ m : ℕ, ∀ l : List V, Fintype.card V - l.length = m → SgmGood F t l →
      ∃ l' : List V, l'.head? = some s ∧ SgmGood F t l' := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro l hm hg
      rcases l with _ | ⟨h, rest⟩
      · exact absurd hg.1 (by simp)
      by_cases hs : h = s
      · exact ⟨h :: rest, by simp [hs], hg⟩
      have hpred : ∃ w, F w h := by
        by_cases ht : h = t
        · subst ht; exact hex_t
        · rcases rest with _ | ⟨x, rest'⟩
          · exfalso; apply ht; simpa using hg.1
          · exact hcons h hs ht x (by simpa using hg.2.2 0 (by simp))
      obtain ⟨w, hw⟩ := hpred
      have hwn : w ∉ h :: rest := by
        intro hmem
        obtain ⟨i, hi, hwi⟩ := List.mem_iff_getElem.mp hmem
        by_cases hi1 : i + 1 < (h :: rest).length
        · have h1 := hg.2.2 i hi1
          rw [hwi] at h1
          have h2 : (h :: rest)[i + 1] = (h :: rest)[0] := hout_uniq w _ _ h1 hw
          have := (hg.2.1.getElem_inj_iff).mp h2
          omega
        · have h3 : i = (h :: rest).length - 1 := by omega
          have h4 := hg.1
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp)] at h4
          subst h3
          have h5 := Option.some.inj h4
          rw [hwi] at h5
          subst h5
          exact hout_t _ hw
      have hnd : (w :: h :: rest).Nodup := List.nodup_cons.mpr ⟨hwn, hg.2.1⟩
      have hlen := hnd.length_le_card
      refine ih (Fintype.card V - (w :: h :: rest).length) ?_ (w :: h :: rest) rfl
        ⟨?_, hnd, ?_⟩
      · simp only [List.length_cons] at hlen hm ⊢
        omega
      · rw [List.getLast?_cons_cons]; exact hg.1
      · intro i hi
        cases i with
        | zero => exact hw
        | succ j =>
          exact hg.2.2 j (by simp only [List.length_cons] at hi ⊢; omega)
  exact H _ [t] rfl ⟨by simp, by simp, by intro i hi; simp at hi⟩

theorem sgm_mem_pathEdges {V : Type*} (p : List V) (e : V × V) (h : e ∈ pathEdges p) :
    ∃ k, ∃ hk : k + 1 < p.length, e = (p[k], p[k + 1]) := by
  rw [pathEdges, List.mem_iff_getElem] at h
  obtain ⟨i, hi, hie⟩ := h
  have hi' : i + 1 < p.length := by simp [List.length_zip] at hi; omega
  refine ⟨i, hi', ?_⟩
  rw [← hie]
  simp [List.getElem_zip, List.getElem_tail]

theorem sgm_path_facts {V : Type*} {n : ℕ} [DecidableEq V] (G : GCS V n) (p : List V)
    (hp : IsPath G p) :
    (∀ k (hk : k + 1 < p.length), (p[k], p[k + 1]) ∈ G.E) ∧
    (∀ k (hk : k + 1 < p.length), (p[k], p[k + 1]) ∈ pathEdges p) ∧
    (∀ h : 0 < p.length, p[0] = G.s) ∧
    (∀ h : 0 < p.length, p[p.length - 1] = G.t) ∧
    (∀ i j (hi : i < p.length) (hj : j < p.length), p[i] = p[j] → i = j) := by
  obtain ⟨hhead, hlast, hnd, hchain⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact List.isChain_iff_getElem.mp hchain k hk
  · intro k hk
    rw [pathEdges, List.mem_iff_getElem]
    refine ⟨k, by simp [List.length_zip]; omega, ?_⟩
    simp [List.getElem_zip, List.getElem_tail]
  · intro h
    have h1 : p[0]? = some G.s := by simpa [List.head?_eq_getElem?] using hhead
    rw [List.getElem?_eq_getElem h] at h1
    exact Option.some.inj h1
  · intro h
    have h1 := hlast
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h1
    exact Option.some.inj h1
  · intro i j hi hj hij
    exact (hnd.getElem_inj_iff).mp hij

theorem sgm_sum_card {α : Type*} [DecidableEq α] (S : Finset α) (y : α → ℝ)
    (hbin : ∀ e ∈ S, y e = 0 ∨ y e = 1) :
    ∑ e ∈ S, y e = ((S.filter fun e => y e = 1).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro e he
  rcases hbin e he with h | h <;> simp [h]

theorem sgm_card_in {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (y : V × V → ℝ) (hbin : ∀ e ∈ G.E, y e = 0 ∨ y e = 1) (v : V) :
    ((G.E.filter fun e => y e = 1 ∧ e.2 = v).card : ℝ) = ∑ e ∈ inEdges G v, y e := by
  rw [sgm_sum_card (inEdges G v) y (fun e he => hbin e (Finset.mem_filter.mp he).1)]
  have : (inEdges G v).filter (fun e => y e = 1) = G.E.filter fun e => y e = 1 ∧ e.2 = v := by
    ext e
    simp only [inEdges, Finset.mem_filter]
    tauto
  rw [this]

theorem sgm_card_out {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (y : V × V → ℝ) (hbin : ∀ e ∈ G.E, y e = 0 ∨ y e = 1) (v : V) :
    ((G.E.filter fun e => y e = 1 ∧ e.1 = v).card : ℝ) = ∑ e ∈ outEdges G v, y e := by
  rw [sgm_sum_card (outEdges G v) y (fun e he => hbin e (Finset.mem_filter.mp he).1)]
  have : (outEdges G v).filter (fun e => y e = 1) = G.E.filter fun e => y e = 1 ∧ e.1 = v := by
    ext e
    simp only [outEdges, Finset.mem_filter]
    tauto
  rw [this]

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (hst : NoInSNoOutT G) (hne : G.s ≠ G.t) (y : V × V → ℝ)
    (hbin : ∀ e ∈ G.E, y e = 0 ∨ y e = 1)
    (hsource : ∑ e ∈ outEdges G G.s, y e = 1) (htarget : ∑ e ∈ inEdges G G.t, y e = 1)
    (hdeg : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ outEdges G v, y e ≤ 1)
    (hcons : ∀ v, v ≠ G.s → v ≠ G.t → ∑ e ∈ inEdges G v, y e = ∑ e ∈ outEdges G v, y e) :
    ∃ p : List V, IsPath G p ∧ (∀ e ∈ pathEdges p, y e = 1) ∧
      (∀ e ∈ G.E, y e = 1 → e ∉ pathEdges p → e.1 ∉ p ∧ e.2 ∉ p) ∧
      ∀ v : V,
        (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.2 = v).card =
            (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.1 = v).card ∧
          (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.1 = v).card ≤ 1 := by
  have hcin := sgm_card_in G y hbin
  have hcout := sgm_card_out G y hbin
  have hFo_s : (G.E.filter fun e => y e = 1 ∧ e.1 = G.s).card = 1 := by
    have := hcout G.s; rw [hsource] at this; exact_mod_cast this
  have hFi_t : (G.E.filter fun e => y e = 1 ∧ e.2 = G.t).card = 1 := by
    have := hcin G.t; rw [htarget] at this; exact_mod_cast this
  have hFo_le : ∀ v, v ≠ G.s → v ≠ G.t → (G.E.filter fun e => y e = 1 ∧ e.1 = v).card ≤ 1 := by
    intro v hs ht
    have h1 := hcout v
    have h2 := hdeg v hs ht
    rw [← h1] at h2
    exact_mod_cast h2
  have hFeq : ∀ v, v ≠ G.s → v ≠ G.t →
      (G.E.filter fun e => y e = 1 ∧ e.2 = v).card =
        (G.E.filter fun e => y e = 1 ∧ e.1 = v).card := by
    intro v hs ht
    have h1 := hcin v
    have h2 := hcout v
    have h3 := hcons v hs ht
    rw [← h1, ← h2] at h3
    exact_mod_cast h3
  -- F-level facts
  let F : V → V → Prop := fun a b => (a, b) ∈ G.E ∧ y (a, b) = 1
  have memFi : ∀ v a, F a v ↔ (a, v) ∈ (G.E.filter fun e => y e = 1 ∧ e.2 = v) := by
    intro v a
    constructor
    · rintro ⟨h1, h2⟩; exact Finset.mem_filter.mpr ⟨h1, h2, rfl⟩
    · intro h
      obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp h
      exact ⟨h1, h2⟩
  have memFo : ∀ v a, F v a ↔ (v, a) ∈ (G.E.filter fun e => y e = 1 ∧ e.1 = v) := by
    intro v a
    constructor
    · rintro ⟨h1, h2⟩; exact Finset.mem_filter.mpr ⟨h1, h2, rfl⟩
    · intro h
      obtain ⟨h1, h2, _⟩ := Finset.mem_filter.mp h
      exact ⟨h1, h2⟩
  have hFi_le : ∀ v, v ≠ G.s → (G.E.filter fun e => y e = 1 ∧ e.2 = v).card ≤ 1 := by
    intro v hs
    by_cases ht : v = G.t
    · subst ht; exact hFi_t.le
    · rw [hFeq v hs ht]; exact hFo_le v hs ht
  have hFo_le' : ∀ v, v ≠ G.t → (G.E.filter fun e => y e = 1 ∧ e.1 = v).card ≤ 1 := by
    intro v ht
    by_cases hs : v = G.s
    · subst hs; exact hFo_s.le
    · exact hFo_le v hs ht
  have hin_uniq : ∀ v a b, F a v → F b v → a = b := by
    intro v a b ha hb
    by_cases hvs : v = G.s
    · exfalso; exact (hst _ ha.1).1 hvs
    · have := Finset.card_le_one.mp (hFi_le v hvs) (a, v) ((memFi v a).mp ha) (b, v)
        ((memFi v b).mp hb)
      exact (Prod.mk.inj this).1
  have hout_uniq : ∀ v a b, F v a → F v b → a = b := by
    intro v a b ha hb
    by_cases hvt : v = G.t
    · exfalso; exact (hst _ ha.1).2 hvt
    · have := Finset.card_le_one.mp (hFo_le' v hvt) (v, a) ((memFo v a).mp ha) (v, b)
        ((memFo v b).mp hb)
      exact (Prod.mk.inj this).2
  have hout_t : ∀ w, ¬ F G.t w := fun w h => (hst _ h.1).2 rfl
  have hnonI : ∀ v, 0 < (G.E.filter fun e => y e = 1 ∧ e.2 = v).card → ∃ a, F a v := by
    intro v h
    obtain ⟨⟨a, b⟩, he⟩ := Finset.card_pos.mp h
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp he
    have h3' : b = v := h3
    subst h3'
    exact ⟨a, h1, h2⟩
  have hex_t : ∃ u, F u G.t := hnonI G.t (by rw [hFi_t]; norm_num)
  have hcons' : ∀ v, v ≠ G.s → v ≠ G.t → ∀ b, F v b → ∃ a, F a v := by
    intro v hs ht b hb
    apply hnonI
    rw [hFeq v hs ht]
    exact Finset.card_pos.mpr ⟨(v, b), (memFo v b).mp hb⟩
  obtain ⟨p, hphead, hgood⟩ := sgm_build F G.s G.t hout_t hout_uniq hex_t hcons'
  have hpath : IsPath G p :=
    ⟨hphead, hgood.1, hgood.2.1, List.isChain_iff_getElem.mpr (fun i h => (hgood.2.2 i h).1)⟩
  obtain ⟨hE, hPE, hp0, hpl, hinj⟩ := sgm_path_facts G p hpath
  have hlen : 0 < p.length := by
    rcases p with _ | ⟨a, r⟩
    · simp at hphead
    · simp
  have hsp : G.s ∈ p := by rw [← hp0 hlen]; exact List.getElem_mem _
  have htp : G.t ∈ p := by rw [← hpl hlen]; exact List.getElem_mem _
  have prop2 : ∀ e ∈ G.E, y e = 1 → e ∉ pathEdges p → e.1 ∉ p ∧ e.2 ∉ p := by
    intro e heE hy hnot
    obtain ⟨u, w⟩ := e
    have hF : F u w := ⟨heE, hy⟩
    constructor
    · intro hu
      obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.mp hu
      by_cases hi1 : i + 1 < p.length
      · have hF2 := hgood.2.2 i hi1
        rw [hiu] at hF2
        have hw := hout_uniq u w _ hF hF2
        apply hnot
        have := hPE i hi1
        rw [hiu, ← hw] at this
        exact this
      · exfalso
        have h3 : i = p.length - 1 := by omega
        subst h3
        have := hpl hlen
        rw [hiu] at this
        exact (hst _ heE).2 this
    · intro hw
      obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hw
      cases i with
      | zero =>
        exfalso
        have := hp0 hlen
        have h5 : w = G.s := hiw.symm.trans this
        exact (hst _ heE).1 h5
      | succ j =>
        have hF2 := hgood.2.2 j (by omega)
        rw [hiw] at hF2
        have hu := hin_uniq w u _ hF hF2
        apply hnot
        have := hPE j (by omega)
        rw [hiw, ← hu] at this
        exact this
  refine ⟨p, hpath, ?_, prop2, ?_⟩
  · intro e he
    obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e he
    exact (hgood.2.2 k hk).2
  · intro v
    by_cases hv : v ∈ p
    · have e1 : (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.2 = v) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (by
          rintro e he ⟨hy, hn, h2⟩
          exact (prop2 e he hy hn).2 (by rw [h2]; exact hv))
      have e2 : (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.1 = v) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (by
          rintro e he ⟨hy, hn, h2⟩
          exact (prop2 e he hy hn).1 (by rw [h2]; exact hv))
      rw [e1, e2]; simp
    · have hvs : v ≠ G.s := fun h => hv (h ▸ hsp)
      have hvt : v ≠ G.t := fun h => hv (h ▸ htp)
      have e1 : (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.2 = v) =
          G.E.filter fun e => y e = 1 ∧ e.2 = v := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
        · rintro ⟨h1, h2, h4⟩
          refine ⟨h1, h2, ?_, h4⟩
          intro hmem
          obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e hmem
          exact hv (by rw [← h4]; exact List.getElem_mem _)
      have e2 : (G.E.filter fun e => y e = 1 ∧ e ∉ pathEdges p ∧ e.1 = v) =
          G.E.filter fun e => y e = 1 ∧ e.1 = v := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
        · rintro ⟨h1, h2, h4⟩
          refine ⟨h1, h2, ?_, h4⟩
          intro hmem
          obtain ⟨k, hk, rfl⟩ := sgm_mem_pathEdges p e hmem
          exact hv (by rw [← h4]; exact List.getElem_mem _)
      rw [e1, e2]
      exact ⟨hFeq v hvs hvt, hFo_le v hvs hvt⟩
