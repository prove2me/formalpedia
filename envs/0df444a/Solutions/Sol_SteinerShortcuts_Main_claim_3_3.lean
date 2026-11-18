-- Prove2me | solution 1 for SteinerShortcuts.Main.claim_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:27:42.87812+00:00
-- url     : https://prove2.me/submissions/b8dc9ca3-3d33-4c56-a658-0d74ee912a57

import Theorems.Thm_SteinerShortcuts_Main_claim_3_1
import Theorems.Thm_SteinerShortcuts_Main_claim_3_4
import Definitions.Def_SteinerShortcuts_Main_TestFunctions
open SteinerShortcuts.Main
set_option maxRecDepth 4000

 theorem step_label (q : ℕ) (v : Point) (t : Fin q) :
    edgeLabel v (step q v t) = (t.val : ℤ) := by
  by_cases ho : v 0 % 2 = 1
  · simp [edgeLabel, step, update, position, direction, ho]
  · simp [edgeLabel, step, update, position, direction, ho]

 theorem step_label_injective (q : ℕ) (v : Point) (a b : Fin q)
    (he : step q v a = step q v b) : a = b := by
  have hh := congrArg (edgeLabel v) he
  rw [step_label, step_label] at hh
  apply Fin.ext
  exact_mod_cast hh

 theorem critical_layer (q : ℕ) (s : Point) (a b : Fin q) (i : ℕ) :
    criticalVertex q s a b i 0 = s 0 + (i : ℤ) := by
  induction i with
  | zero => simp [criticalVertex]
  | succ i ih => simp [criticalVertex, step, update, ih]; ring

private theorem chain_zip {V : Type} (r : V → V → Prop) (a : V) (l : List V) :
    (a::l).IsChain r ↔ ∀ e ∈ (a::l).zip l, r e.1 e.2 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp [List.isChain_cons_cons, ih]

 theorem critical_arcs (L q : ℕ) (s : Point) (a b : Fin q)
    (e : Point × Point) (he : e ∈ (critical L q s a b).arcs) :
    ∃ i < L-1, e.1 = criticalVertex q s a b i ∧
      e.2 = criticalVertex q s a b (i+1) := by
  let f := criticalVertex q s a b
  have hc : ((List.range (L-1+1)).map f).IsChain
      (fun v w => ∃ i < L-1, v = f i ∧ w = f (i+1)) := by
    rw [List.isChain_map, List.isChain_range_succ]
    intro i hi
    exact ⟨i,hi,rfl,rfl⟩
  have heq : (critical L q s a b).vertices = (List.range (L-1+1)).map f := by
    simp [Route.vertices, critical, List.range_succ_eq_map, List.map_map, f,
      Function.comp_def, criticalVertex]
  rw [← heq] at hc
  exact (chain_zip _ _ _).mp hc e he

 theorem vanishes_critical (L q : ℕ) (s : Point) (a b : Fin q) (F : TestFunction q)
    (hf : ∀ i < L-1, F (position (criticalVertex q s a b i))
      (if i%2=0 then a else b) = 0) : Vanishes F (critical L q s a b) := by
  intro e he t ht
  obtain ⟨i,hi,hv,hw⟩ := critical_arcs L q s a b e he
  have he : step q e.1 t = step q e.1 (if i%2=0 then a else b) := by
    rw [← ht, hv, hw]
    rfl
  have hlabel := step_label_injective q e.1 t _ he
  rw [hlabel,hv]
  exact hf i hi


open SteinerShortcuts.Main

private theorem fin_of_zmod_eq (q : ℕ) (a b : Fin q)
    (he : (a.val : ZMod q) = (b.val : ZMod q)) : a = b := by
  have := congrArg ZMod.val he
  apply Fin.ext
  simpa [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using this

private theorem labelY_mod (q : ℕ) [NeZero q] (t : Fin q) :
    ((labelY q t.val : ℤ) : ZMod q) = (t.val : ZMod q)^2 := by
  simp [labelY]

 theorem label_line (q : ℕ) (hq : q.Prime) (a b t : Fin q)
    (he : (labelY q t.val : ℝ) - lineSlope q a b * (t.val:ℝ) -
      lineIntercept q a b = 0) : t = a ∨ t = b := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : NeZero q := ⟨hq.ne_zero⟩
  by_cases hab : a = b
  · subst b
    have hreal : (labelY q t.val : ℝ) - (labelY q a.val : ℝ) =
        2*(a.val:ℝ)*((t.val:ℝ)-(a.val:ℝ)) := by
      simp [lineSlope, lineIntercept] at he
      linarith
    have hint : labelY q t.val - labelY q a.val =
        2*(a.val:ℤ)*((t.val:ℤ)-(a.val:ℤ)) := by exact_mod_cast hreal
    have hm := congrArg (fun z : ℤ => (z : ZMod q)) hint
    push_cast at hm
    simp only [labelY_mod] at hm
    have hz : ((t.val : ZMod q) - (a.val : ZMod q))^2 = 0 := by linear_combination hm
    have heq : (t.val : ZMod q) = (a.val : ZMod q) := by
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    exact Or.inl (fin_of_zmod_eq q t a heq)
  · have hd : (b.val:ℝ)-(a.val:ℝ) ≠ 0 := by
      intro h
      apply hab
      apply Fin.ext
      exact_mod_cast (sub_eq_zero.mp h).symm
    have hreal : ((labelY q t.val:ℝ)-(labelY q a.val:ℝ))*((b.val:ℝ)-(a.val:ℝ)) =
        ((labelY q b.val:ℝ)-(labelY q a.val:ℝ))*((t.val:ℝ)-(a.val:ℝ)) := by
      simp [lineIntercept, lineSlope, hab] at he
      field_simp at he
      nlinarith [he]
    have hint : (labelY q t.val-labelY q a.val)*((b.val:ℤ)-(a.val:ℤ)) =
        (labelY q b.val-labelY q a.val)*((t.val:ℤ)-(a.val:ℤ)) := by exact_mod_cast hreal
    have hm := congrArg (fun z : ℤ => (z : ZMod q)) hint
    push_cast at hm
    simp only [labelY_mod] at hm
    have hz : ((t.val:ZMod q)-(a.val:ZMod q))*((t.val:ZMod q)-(b.val:ZMod q))*
        ((b.val:ZMod q)-(a.val:ZMod q)) = 0 := by linear_combination hm
    rcases mul_eq_zero.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hz
      · exact Or.inl (fin_of_zmod_eq q t a (sub_eq_zero.mp hz))
      · exact Or.inr (fin_of_zmod_eq q t b (sub_eq_zero.mp hz))
    · exact False.elim (hab (fin_of_zmod_eq q a b (sub_eq_zero.mp hz).symm))

private theorem line_zero_left (q : ℕ) (a b : Fin q) :
    (labelY q a.val : ℝ) - lineSlope q a b * (a.val:ℝ) - lineIntercept q a b = 0 := by
  unfold lineIntercept
  ring

private theorem line_zero_right (q : ℕ) (a b : Fin q) :
    (labelY q b.val : ℝ) - lineSlope q a b * (b.val:ℝ) - lineIntercept q a b = 0 := by
  by_cases hab : a = b
  · subst b; exact line_zero_left q a a
  · have hd : (b.val:ℝ)-(a.val:ℝ) ≠ 0 := by
      intro he; apply hab; apply Fin.ext; exact_mod_cast (sub_eq_zero.mp he).symm
    unfold lineIntercept lineSlope
    rw [if_neg hab]
    field_simp
    ring

private theorem source_layer (L q : ℕ) (s : Point) (hs : s ∈ sources L q) : s 0 = 1 := by
  have hh := Fintype.mem_piFinset.mp hs 0
  simpa [layerBox] using hh

private theorem Y_critical (L q : ℕ) (P Q : CriticalData q) (hp : P.Valid L) (hq : Q.Valid L) :
    Vanishes (testY P Q) (P.route L) ∧ Vanishes (testY P Q) (Q.route L) := by
  have f (S : CriticalData q) (hs : S.Valid L)
      (ha : S.a = P.a ∨ S.a = Q.a) (hb : S.b = P.b ∨ S.b = Q.b) :
      Vanishes (testY P Q) (S.route L) := by
    apply vanishes_critical
    intro i hi
    have h0 := critical_layer q S.source S.a S.b i
    rw [source_layer L q S.source hs] at h0
    by_cases ho : i % 2 = 0
    · have ho' : criticalVertex q S.source S.a S.b i 0 % 2 = 1 := by omega
      simp [testY, position, ho, ho']
      rcases ha with ha | ha
      · rw [ha, line_zero_left]
      · rw [ha, line_zero_right]
    · have ho' : criticalVertex q S.source S.a S.b i 0 % 2 ≠ 1 := by omega
      simp [testY, position, ho, ho']
      rcases hb with hb | hb
      · rw [hb, line_zero_left]
      · rw [hb, line_zero_right]
  exact ⟨f P hp (Or.inl rfl) (Or.inl rfl), f Q hq (Or.inr rfl) (Or.inr rfl)⟩

private theorem route_edge (R : Route Point) (i : ℕ) (hi : i < R.length) :
    ∃ v w, R.vertices[i]? = some v ∧ R.vertices[i+1]? = some w ∧ (v,w) ∈ R.arcs := by
  have hiv : i < R.vertices.length := by simpa [Route.vertices, Route.length] using Nat.lt_succ_of_lt hi
  have hit : i < R.tail.length := hi
  have hia : i < R.arcs.length := by simpa [Route.arcs, Route.vertices, Route.length] using hi
  refine ⟨R.vertices[i], R.tail[i], List.getElem?_eq_getElem hiv, ?_, ?_⟩
  · simpa only [Route.vertices, List.getElem?_cons_succ] using List.getElem?_eq_getElem hit
  · have hm := List.getElem_mem hia
    simpa only [Route.arcs, List.getElem_zip] using hm

private theorem Q1_of_Y (L q : ℕ) (hq : q.Prime) (P Q : CriticalData q)
    (R : Route Point) (hp : IsPath (construction L q) R) (hv : Vanishes (testY P Q) R) :
    Q1 P Q R := by
  intro i hi
  obtain ⟨v,w,hv',hw',he⟩ := route_edge R i hi
  have ha := (chain_zip _ _ _).mp hp (v,w) he
  obtain ⟨_,_,_,t,ht⟩ := ha
  change w = step q v t at ht
  have hz := hv (v,w) he t ht
  have hlabel : edgeLabel v w = (t.val:ℤ) := by rw [ht,step_label]
  constructor
  · intro ho
    obtain ⟨u,hu,ho⟩ := ho
    have huv : u = v := Option.some.inj (hu.symm.trans hv')
    subst u
    have hy : (labelY q t.val : ℝ) - lineSlope q P.a Q.a * (t.val:ℝ) -
        lineIntercept q P.a Q.a = 0 := by
      apply sq_eq_zero_iff.mp
      simpa [testY, position, ho] using hz
    rcases label_line q hq P.a Q.a t hy with hh | hh
    · exact Or.inl ⟨v,w,hv',hw',by simpa [hh] using hlabel⟩
    · exact Or.inr ⟨v,w,hv',hw',by simpa [hh] using hlabel⟩
  · intro ho
    obtain ⟨u,hu,ho⟩ := ho
    have huv : u = v := Option.some.inj (hu.symm.trans hv')
    subst u
    have hodd : v 0 % 2 ≠ 1 := by omega
    have hy : (labelY q t.val : ℝ) - lineSlope q P.b Q.b * (t.val:ℝ) -
        lineIntercept q P.b Q.b = 0 := by
      apply sq_eq_zero_iff.mp
      simpa [testY, position, hodd] using hz
    rcases label_line q hq P.b Q.b t hy with hh | hh
    · exact Or.inl ⟨v,w,hv',hw',by simpa [hh] using hlabel⟩
    · exact Or.inr ⟨v,w,hv',hw',by simpa [hh] using hlabel⟩

 theorem solution (L q : ℕ) (h : Admissible L q) (P Q : CriticalData q)
    (R T : Route Point) (hs : PairSetup L q P Q R T) :
    Q1 P Q R ∧ Q1 Q P T := by
  have hn : T1prime (testY P Q) R T := by
    constructor <;> intro e he t ht <;> exact sq_nonneg _
  have hl := claim_3_4 L q h P Q R T hs
  have hz := claim_3_1 L q h P Q R T hs (testY P Q) hn (Y_critical L q P Q hs.1 hs.2.1) hl
  refine ⟨Q1_of_Y L q h.2.2.1 P Q R hs.2.2.2.1.1 hz.1, ?_⟩
  have ht := Q1_of_Y L q h.2.2.1 P Q T hs.2.2.2.2.1 hz.2
  intro i hi
  have hh := ht i hi
  exact ⟨fun ho => (hh.1 ho).symm, fun he => (hh.2 he).symm⟩
